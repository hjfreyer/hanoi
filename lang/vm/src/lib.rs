use bytecode::{Instruction, Library, SentenceIndex, Value};

pub mod runtime;
pub use runtime::{DefaultEnvironment, Environment, Runtime};

use bytecode::value::numeric_cmp;

/// A pending return: where to resume, plus any values `Dip` hid from the callee.
///
/// `hidden` is empty for `Jump` and `Branch`, which give the callee the top of
/// the stack. It is restored above whatever the callee leaves behind.
struct Frame {
    sentence: SentenceIndex,
    ip: usize,
    hidden: Vec<Value>,
}

/// The virtual machine that executes sentences from a loaded library.
pub struct VM {
    library: Library,
    stack: Vec<Value>,
    call_stack: Vec<Frame>,
    tracing: bool,
    gas_limit: Option<u64>,
    steps_executed: u64,
}

impl VM {
    /// Creates a new VM initialized with the given library.
    pub fn new(library: Library) -> Self {
        Self {
            library,
            stack: Vec::new(),
            call_stack: Vec::new(),
            tracing: false,
            gas_limit: None,
            steps_executed: 0,
        }
    }

    /// Enables or disables detailed operation-by-operation tracing.
    pub fn set_tracing(&mut self, tracing: bool) {
        self.tracing = tracing;
    }

    /// Sets the maximum number of VM steps allowed during execution.
    pub fn set_gas_limit(&mut self, gas_limit: Option<u64>) {
        self.gas_limit = gas_limit;
    }

    /// Returns the number of steps executed during the last run.
    pub fn steps_executed(&self) -> u64 {
        self.steps_executed
    }

    /// Returns a slice representing the current stack.
    pub fn stack(&self) -> &[Value] {
        &self.stack
    }

    /// Helper to pop a value from the stack, returning an error on underflow.
    fn pop(&mut self) -> Result<Value, String> {
        self.stack
            .pop()
            .ok_or_else(|| "Stack underflow".to_string())
    }

    /// Executes sentences in the library starting with the given `start_sentence`.
    /// Reaching the end of a sentence pops the call stack to return to the caller.
    /// Execution terminates when the call stack is empty and the current sentence ends.
    pub fn execute(&mut self, start_sentence: SentenceIndex) -> Result<(), String> {
        let mut current_sentence = start_sentence;
        let mut ip = 0;
        self.steps_executed = 0;

        loop {
            // Get the sentence reference
            let sentence = self
                .library
                .sentences
                .get(current_sentence)
                .ok_or_else(|| format!("Invalid sentence index: {:?}", current_sentence))?;

            if ip >= sentence.len() {
                // Return to the caller if there's an address on the call stack
                if let Some(frame) = self.call_stack.pop() {
                    if self.tracing {
                        println!(
                            "[TRACE] Returning to Sentence: {:?}, IP: {}",
                            frame.sentence, frame.ip
                        );
                    }
                    // Values hidden by Dip go back above the callee's results.
                    self.stack.extend(frame.hidden);
                    current_sentence = frame.sentence;
                    ip = frame.ip;
                    continue;
                } else {
                    if self.tracing {
                        println!("[TRACE] Finished execution");
                    }
                    // Terminate execution if the call stack is empty
                    break;
                }
            }

            // Clone the instruction to release the borrow on self.library
            let instruction = sentence[ip].clone();
            if self.tracing {
                println!(
                    "[TRACE] Sentence: {:?}, IP: {}, Instruction: {} | Stack: {:?}",
                    current_sentence, ip, instruction, self.stack
                );
            }
            ip += 1;

            if let Some(limit) = self.gas_limit
                && self.steps_executed >= limit
            {
                return Err("gas limit exceeded".to_string());
            }
            self.steps_executed += 1;

            match instruction {
                Instruction::Push(value) => {
                    self.stack.push(value);
                }
                Instruction::Drop => {
                    if self.stack.is_empty() {
                        return Err("Stack underflow on Drop".to_string());
                    }
                    self.stack.pop();
                }
                Instruction::Copy => {
                    let Some(top) = self.stack.last() else {
                        return Err("Stack underflow on Copy".to_string());
                    };
                    let val = top.clone();
                    self.stack.push(val);
                }
                Instruction::Swap => {
                    if self.stack.len() < 2 {
                        return Err(format!(
                            "Stack underflow on Swap: stack size {}",
                            self.stack.len()
                        ));
                    }
                    let top = self.stack.len() - 1;
                    self.stack.swap(top, top - 1);
                }
                Instruction::Equal => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(Value::Bool(a == b));
                }
                Instruction::Greater | Instruction::Less => {
                    // A NaN is unordered rather than non-numeric, but neither
                    // pair yields an ordering and neither is a comparison this
                    // instruction can claim to have made. `false` is what it
                    // answers where there is no ordering to report, which is
                    // the same answer it gives for an ordering that does not
                    // hold — see `docs/totality.md`.
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let want = if matches!(instruction, Instruction::Greater) {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Less
                    };
                    let answer = numeric_cmp(&a, &b).is_some_and(|ord| ord == want);
                    self.stack.push(Value::Bool(answer));
                }
                Instruction::Add => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(match (a, b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_add(y)),
                        _ => Value::Int(0),
                    });
                }
                Instruction::Subtract => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(match (a, b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_sub(y)),
                        _ => Value::Int(0),
                    });
                }
                Instruction::Multiply => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(match (a, b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_mul(y)),
                        _ => Value::Int(0),
                    });
                }
                Instruction::Divide => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(match (a, b) {
                        // Division by zero has no answer to give, so it takes
                        // the same `0` every other off-domain pair does.
                        (Value::Int(_), Value::Int(0)) => Value::Int(0),
                        // `wrapping_div` keeps `i64::MIN / -1` from being a
                        // host-level overflow.
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_div(y)),
                        _ => Value::Int(0),
                    });
                }
                Instruction::Modulo => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(match (a, b) {
                        (Value::Int(_), Value::Int(0)) => Value::Int(0),
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_rem(y)),
                        _ => Value::Int(0),
                    });
                }
                Instruction::Not => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(!val.truthy()));
                }
                Instruction::And => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(Value::Bool(a.truthy() && b.truthy()));
                }
                Instruction::Or => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(Value::Bool(a.truthy() || b.truthy()));
                }
                Instruction::Negate => {
                    let val = self.pop()?;
                    self.stack.push(match val {
                        Value::Int(x) => Value::Int(x.wrapping_neg()),
                        _ => Value::Int(0),
                    });
                }
                Instruction::Jump(target) => {
                    self.call_stack.push(Frame {
                        sentence: current_sentence,
                        ip,
                        hidden: Vec::new(),
                    });
                    current_sentence = target;
                    ip = 0;
                }
                Instruction::Dip(target) => {
                    // Withhold the top value for the duration of the call. One
                    // value: a deeper region is this many frames deep, and
                    // each of them hides its own.
                    let Some(hidden) = self.stack.pop() else {
                        return Err("Stack underflow on Dip".to_string());
                    };
                    self.call_stack.push(Frame {
                        sentence: current_sentence,
                        ip,
                        hidden: vec![hidden],
                    });
                    current_sentence = target;
                    ip = 0;
                }
                Instruction::Branch(then_target, else_target) => {
                    let cond = self.pop()?;
                    // The then arm is reached by `Bool(true)` and nothing else;
                    // every other value takes the else arm, agreeing with junk
                    // being falsy everywhere.
                    let b = cond.truthy();
                    // Push the return address (the next instruction) to the call stack
                    self.call_stack.push(Frame {
                        sentence: current_sentence,
                        ip,
                        hidden: Vec::new(),
                    });
                    if b {
                        current_sentence = then_target;
                    } else {
                        current_sentence = else_target;
                    }
                    ip = 0;
                }
                Instruction::Tuple(n) => {
                    if self.stack.len() < n {
                        return Err(format!(
                            "Stack underflow on Tuple: requested {} but stack size {}",
                            n,
                            self.stack.len()
                        ));
                    }
                    // The elements keep the order they had on the stack, so the
                    // *deepest* becomes element 0 and the topmost the last:
                    // `push 1 ; push 2 ; tuple 2` is `(1, 2)`.
                    let index = self.stack.len() - n;
                    let elements = self.stack.split_off(index);
                    self.stack.push(Value::Tuple(elements));
                }
                Instruction::Untuple(n) => {
                    // `as_tuple n ; untuple n`, which is the whole definition:
                    // a value that is not a tuple of exactly `n` is coerced to
                    // the one that is — `n` copies of `()` — and then taken
                    // apart like any other. A caller that needs to know which
                    // of the two happened asks before it unpacks, with `pick 0
                    // ; as_tuple n ; equal`. See `docs/totality.md`.
                    let val = self.pop()?;
                    match val {
                        // Element 0 goes back to the deepest slot, which is
                        // where `tuple n` found it.
                        Value::Tuple(elements) if elements.len() == n => {
                            self.stack.extend(elements)
                        }
                        _ => self.stack.extend(std::iter::repeat_n(Value::unit(), n)),
                    }
                }
                Instruction::IsInt => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(val, Value::Int(_))));
                }
                Instruction::IsBool => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(val, Value::Bool(_))));
                }
                Instruction::IsConstString => {
                    let val = self.pop()?;
                    self.stack
                        .push(Value::Bool(matches!(val, Value::ConstString(_))));
                }
                Instruction::IsSymbol => {
                    let val = self.pop()?;
                    self.stack
                        .push(Value::Bool(matches!(val, Value::Symbol(_))));
                }
                Instruction::IsTuple(width) => {
                    // A width asks the whole question: a tuple of the wrong
                    // length is as much a mismatch as a symbol, being
                    // exactly what `untuple n` could not take apart.
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(
                        val,
                        Value::Tuple(elements) if width.is_none_or(|n| elements.len() == n)
                    )));
                }
                Instruction::TupleLength => {
                    // A length is an `Int` whatever it was asked about, so a
                    // non-tuple takes the same `0` the arithmetic does rather
                    // than coming back out where a count belongs.
                    let val = self.pop()?;
                    self.stack.push(match val {
                        Value::Tuple(elements) => Value::Int(elements.len() as i64),
                        _ => Value::Int(0),
                    });
                }
                // The three coercions. Each leaves one value of the type it
                // names, whatever it was handed. See `docs/totality.md`.
                Instruction::AsBool => {
                    // The identity on a `Bool`, since `truthy(Bool(p)) = p`,
                    // and the same coercion `branch`, `not`, `and` and `or`
                    // apply to their operands anyway.
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(val.truthy()));
                }
                Instruction::AsInt => {
                    let val = self.pop()?;
                    self.stack.push(match val {
                        int @ Value::Int(_) => int,
                        _ => Value::Int(0),
                    });
                }
                Instruction::AsTuple(n) => {
                    // A tuple of the wrong width is a mismatch like any other:
                    // it is exactly what `untuple n` could not take apart, so
                    // the junk is a tuple that it can.
                    let val = self.pop()?;
                    self.stack.push(match val {
                        Value::Tuple(elements) if elements.len() == n => Value::Tuple(elements),
                        _ => Value::Tuple(vec![Value::unit(); n]),
                    });
                }
                Instruction::ConstStringLen => {
                    let val = self.pop()?;
                    self.stack.push(match val {
                        Value::ConstString(ref s) => Value::Int(s.chars().count() as i64),
                        _ => Value::Int(0),
                    });
                }
                Instruction::ConstStringCharAt => {
                    let idx_val = self.pop()?;
                    let str_val = self.pop()?;
                    // Wrong types and an out-of-range index answer alike: an
                    // index is in range or it is not, and there is nothing for
                    // a caller to learn from telling the two apart. A caller
                    // that wants the question asked has `const_string_len` and
                    // `less` to ask it with.
                    let ch = match (str_val, idx_val) {
                        (Value::ConstString(s), Value::Int(idx)) => usize::try_from(idx)
                            .ok()
                            .and_then(|idx| s.chars().nth(idx))
                            .map(|ch| ch as i64),
                        _ => None,
                    };
                    self.stack.push(Value::Int(ch.unwrap_or(0)));
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::{Library, SentenceIndex, Value};

    #[test]
    fn test_simple_arithmetic() {
        let mut library = Library::new();
        let sentence = vec![
            Instruction::Push(Value::Int(10)),
            Instruction::Push(Value::Int(20)),
            Instruction::Add,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(30)]);
    }

    #[test]
    fn test_stack_manipulation() {
        let mut library = Library::new();
        let sentence = vec![
            Instruction::Push(Value::Int(5)),
            Instruction::Copy,
            Instruction::Push(Value::Int(10)),
            Instruction::Swap,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(5), Value::Int(10), Value::Int(5)]);
    }

    #[test]
    fn test_branching() {
        let mut library = Library::new();

        // idx 0: Push true, Branch to idx 1, else idx 2. The arm that runs is
        // the one the stack says, and which value comes back says which.
        let s0 = vec![
            Instruction::Push(Value::Bool(true)),
            Instruction::Branch(SentenceIndex::from(1), SentenceIndex::from(2)),
        ];
        let s1 = vec![Instruction::Push(Value::Int(42))];
        let s2 = vec![Instruction::Push(Value::Int(0))];

        library.sentences.push(s0);
        library.sentences.push(s1);
        library.sentences.push(s2);

        let mut vm = VM::new(library);
        assert!(vm.execute(SentenceIndex::from(0)).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(42)]);
    }

    #[test]
    fn test_call_stack_return() {
        let mut library = Library::new();

        // sentence 0: Push 10, call sentence 1, and what comes back says that
        // sentence 1 ran and returned here.
        let s0 = vec![
            Instruction::Push(Value::Int(10)),
            Instruction::Jump(SentenceIndex::from(1)),
            Instruction::Equal,
        ];

        // sentence 1: Push 10
        let s1 = vec![Instruction::Push(Value::Int(10))];

        library.sentences.push(s0);
        library.sentences.push(s1);

        let mut vm = VM::new(library);
        assert!(vm.execute(SentenceIndex::from(0)).is_ok());
        assert_eq!(vm.stack(), &[Value::Bool(true)]);
    }

    #[test]
    fn test_dip_hides_the_top_of_stack() {
        let mut library = Library::new();

        // sentence 0: [1, 2, 99], dip past 99 and add, expecting [3, 99].
        let s0 = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Push(Value::Int(99)),
            Instruction::Dip(SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Add];

        library.sentences.push(s0);
        library.sentences.push(s1);

        let mut vm = VM::new(library);
        assert!(vm.execute(SentenceIndex::from(0)).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(3), Value::Int(99)]);
    }

    #[test]
    fn test_dip_zero_is_jump() {
        let mut library = Library::new();

        let s0 = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Jump(SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Add];

        library.sentences.push(s0);
        library.sentences.push(s1);

        let mut vm = VM::new(library);
        assert!(vm.execute(SentenceIndex::from(0)).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(3)]);
    }

    #[test]
    fn test_dip_nests() {
        let mut library = Library::new();

        // The hidden regions accumulate: dip 1 { dip 1 { add } } over
        // [1, 2, 8, 9] reaches the 1 and 2 and leaves the 8 and 9 in place.
        let s0 = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Push(Value::Int(8)),
            Instruction::Push(Value::Int(9)),
            Instruction::Dip(SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Dip(SentenceIndex::from(2))];
        let s2 = vec![Instruction::Add];

        library.sentences.push(s0);
        library.sentences.push(s1);
        library.sentences.push(s2);

        let mut vm = VM::new(library);
        assert!(vm.execute(SentenceIndex::from(0)).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(3), Value::Int(8), Value::Int(9)]);
    }

    #[test]
    fn test_dip_underflow() {
        let mut library = Library::new();

        // A frame hides one value, so an empty stack is the whole of what it
        // takes to have nothing to hide.
        let s0 = vec![Instruction::Dip(SentenceIndex::from(1))];
        let s1 = vec![];

        library.sentences.push(s0);
        library.sentences.push(s1);

        let mut vm = VM::new(library);
        let res = vm.execute(SentenceIndex::from(0));
        assert!(res.unwrap_err().contains("Stack underflow on Dip"));
    }

    #[test]
    fn test_tuples() {
        let mut library = Library::new();
        // push 1, push 2, push 3, tuple(3) -> Tuple(1, 2, 3)
        // untuple(3) -> pushes 1, 2, 3 back.
        let sentence = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Push(Value::Int(3)),
            Instruction::Tuple(3),
            Instruction::Untuple(3),
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(1), Value::Int(2), Value::Int(3)]);
    }

    #[test]
    fn test_type_checks_and_tuple_length() {
        let mut library = Library::new();
        // Each answer is left where the assertion below can read it.
        let sentence = vec![
            Instruction::Push(Value::Int(42)),
            Instruction::IsInt,
            Instruction::Push(Value::Bool(true)),
            Instruction::IsInt,
            Instruction::Push(Value::Bool(true)),
            Instruction::IsBool,
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Tuple(2),
            Instruction::IsTuple(None),
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Tuple(2),
            Instruction::IsTuple(Some(2)),
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Tuple(2),
            Instruction::IsTuple(Some(3)),
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Tuple(2),
            Instruction::TupleLength,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert_eq!(
            vm.stack(),
            &[
                Value::Bool(true),  // 42 is an int
                Value::Bool(false), // true is not
                Value::Bool(true),  // true is a bool
                Value::Bool(true),  // (1, 2) is a tuple
                Value::Bool(true),  // of exactly two
                Value::Bool(false), // and so not of three
                Value::Int(2),      // and two long
            ]
        );
    }

    #[test]
    fn test_integration_assembler_vm() {
        let code = r#"
            export sentence start {
                push 10
                push 20
                add
                // Stack: [30]

                // Test branching with inline targets
                push true
                branch {
                    push 100
                } {
                    push 200
                }
                // Stack: [30, 100]
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let start_idx = *res.exports.get("start").unwrap();

        let mut vm = VM::new(res);
        assert!(vm.execute(start_idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(30), Value::Int(100)]);
    }

    #[test]
    fn test_symbols_vm() {
        let code = r#"
            symbol status_ok
            symbol status_error
            
            export sentence entry {
                push status_ok
                jump verify
            }
            
            sentence verify {
                // Top of stack has the passed symbol. Compare it to status_ok.
                push status_ok
                equal

                // Compare it to status_error (should not be equal)
                push status_ok
                push status_error
                equal
                not
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let entry_idx = *res.exports.get("entry").unwrap();

        let mut vm = VM::new(res);
        assert!(vm.execute(entry_idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Bool(true), Value::Bool(true)]);
    }

    #[test]
    fn test_const_string_len_and_char_at() {
        let code = r#"
            const_string ascii_str "hello"
            const_string unicode_str "café"
            
            export sentence test_len {
                push ascii_str
                const_string_len
                push unicode_str
                const_string_len
            }

            export sentence test_char_at {
                push ascii_str
                push 1
                const_string_char_at
                push unicode_str
                push 3
                const_string_char_at
            }

            export sentence test_out_of_bounds {
                push unicode_str
                push 4
                const_string_char_at
                // Out of range, and the 0 it answers with is the same 0 a
                // string of zeros would have given: nothing here tells the two
                // apart, and a caller that must have `const_string_len` and
                // `less` to ask with.
            }
        "#;
        let res = bytecode::assemble(code).unwrap();

        // Run test_len: each length, and nothing else.
        let test_len_idx = *res.exports.get("test_len").unwrap();
        let mut vm = VM::new(res.clone());
        assert!(vm.execute(test_len_idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(5), Value::Int(4)]);

        // Run test_char_at
        let test_char_idx = *res.exports.get("test_char_at").unwrap();
        let mut vm = VM::new(res.clone());
        assert!(vm.execute(test_char_idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(101), Value::Int(233)]);

        // Run test_out_of_bounds: an index past the end answers 0 rather than
        // failing.
        let oob_idx = *res.exports.get("test_out_of_bounds").unwrap();
        let mut vm = VM::new(res);
        assert!(vm.execute(oob_idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(0)]);
    }

    #[test]
    fn test_tracing_execution() {
        let code = r#"
            export sentence entry {
                push 42
                push 100
                add
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let entry_idx = *res.exports.get("entry").unwrap();
        let mut vm = VM::new(res);
        vm.set_tracing(true);
        assert!(vm.execute(entry_idx).is_ok());
        assert_eq!(vm.stack(), &[Value::Int(142)]);
    }

    #[test]
    fn test_compose_rename_prefix() {
        let code = r#"
            mod prelude {
                mod event {
                    symbol tau
                }
                symbol start
                symbol pass
                symbol fail
            }

            symbol from_sym
            symbol to_sym
            symbol payload
            mod base {
                export function init {
                    // `untuple 0` takes the argument whether or not it was
                    // `()`, which is the whole of what it does.
                    untuple 0
                    push 0
                }
                export function accept {
                    // `untuple 2` leaves two values either way, so this reads
                    // the same on a malformed event: it just answers about the
                    // `()`s that stood in for the parts.
                    untuple 2
                    drop 0
                    push crate::payload
                    equal
                }
                export function emit {
                    drop 0
                    push crate::payload
                    push true
                    tuple 2
                }
                export function process {
                    untuple 2
                    drop 0
                    drop 0
                    push 1
                }
                export function is_done {
                    drop 0
                    push false
                }
                export function is_ready_to_finish {
                    drop 0
                    push false
                }
                export function tau_reduce {
                    push false
                    tuple 2
                }
            }

            mod prefixed compose_prefix(base, from_sym);
            mod renamed compose_rename_prefix(from_sym, to_sym, prefixed);

            // Each query is its own sentence, so what it answers is the whole
            // stack the VM is left holding.
            export sentence test_accept {
                tuple 0
                jump renamed::init
                // Stack: [state] (which is 0)
                push payload
                push to_sym
                tuple 2
                roll 1
                tuple 2
                jump renamed::accept
            }

            export sentence test_emit {
                tuple 0
                jump renamed::init
                jump renamed::emit
            }

            export sentence test_process {
                tuple 0
                jump renamed::init
                // Process event (payload, to_sym) -> rewrites to (payload, from_sym)
                push payload
                push to_sym
                tuple 2
                roll 1
                tuple 2
                jump renamed::process
                // Stack: [1] (new_state)
                jump renamed::tau_reduce
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let payload = res.symbols.get("payload").unwrap().clone();
        let to_sym = res.symbols.get("to_sym").unwrap().clone();
        let renamed_event = Value::Tuple(vec![payload, to_sym]);

        // The renamed machine takes the event under its new name.
        let idx = *res.exports.get("test_accept").unwrap();
        let mut vm = VM::new(res.clone());
        vm.execute(idx).expect("test_accept");
        assert_eq!(vm.stack(), &[Value::Bool(true)]);

        // And emits under it too.
        let idx = *res.exports.get("test_emit").unwrap();
        let mut vm = VM::new(res.clone());
        vm.execute(idx).expect("test_emit");
        assert_eq!(
            vm.stack(),
            &[Value::Tuple(vec![renamed_event, Value::Bool(true)])]
        );

        // Processing advances the state, and nothing reduces from there.
        let idx = *res.exports.get("test_process").unwrap();
        let mut vm = VM::new(res);
        vm.execute(idx).expect("test_process");
        assert_eq!(
            vm.stack(),
            &[Value::Tuple(vec![Value::Int(1), Value::Bool(false)])]
        );

        // Also test argument count error
        let bad_code = r#"
            symbol a
            symbol b
            mod m {
                export function init { untuple 0 push 0 }
                export sentence accept { untuple 2 drop 0 drop 0 push false }
                export function emit { drop 0 tuple 0 push false tuple 2 }
                export sentence process { }
            }
            mod bad compose_rename_prefix(a, m);
        "#;
        assert!(bytecode::assemble(bad_code).is_err());
    }

    #[test]
    fn test_compose_static_closure() {
        let code = r#"
            mod base {
                export function init {
                    // Stack has the value pushed by the composer
                    push 10
                    add
                }
                export function accept {
                    untuple 2
                    drop 0
                    drop 0
                    push false
                }
                export function emit {
                    drop 0
                    tuple 0
                    push false
                    tuple 2
                }
                export function process {
                    untuple 2
                    drop 1
                    push 100
                    add
                }
                export function tau_reduce {
                    push false
                    tuple 2
                }
                export function is_done {
                    drop 0
                    push false
                }
                export function is_ready_to_finish {
                    drop 0
                    push false
                }
            }

            mod closed compose_static_closure(base, 42);

            // Initialize state: should push 42, then call base::init which adds 10 -> returns 52
            export sentence test_init {
                tuple 0
                jump closed::init
            }

            // Call process: should push 100, then add -> 152
            export sentence test_process {
                tuple 0
                jump closed::init
                push 0
                roll 1
                tuple 2
                jump closed::process
            }
        "#;
        let res = bytecode::assemble(code).unwrap();

        let idx = *res.exports.get("test_init").unwrap();
        let mut vm = VM::new(res.clone());
        vm.execute(idx).expect("test_init");
        assert_eq!(vm.stack(), &[Value::Int(52)]);

        let idx = *res.exports.get("test_process").unwrap();
        let mut vm = VM::new(res);
        vm.execute(idx).expect("test_process");
        assert_eq!(vm.stack(), &[Value::Int(152)]);
    }

    #[test]
    fn test_tau_reduce() {
        let code = r#"
            mod m_no_tau {
                export function init {
                    untuple 0
                    push 0
                }
                export sentence accept {
                    untuple 2
                    drop 0
                    drop 0
                    push false
                }
                export function emit {
                    drop 0
                    tuple 0
                    push false
                    tuple 2
                }
                export function tau_reduce {
                    push false
                    tuple 2
                }
                export function process {
                    untuple 2
                    drop 1
                }
                export function is_done {
                    drop 0
                    push false
                }
                export function is_ready_to_finish {
                    drop 0
                    push false
                }
            }

            mod m_with_tau {
                export function init {
                    untuple 0
                    push 0
                }
                export sentence accept {
                    untuple 2
                    drop 0
                    drop 0
                    push false
                }
                export function emit {
                    drop 0
                    tuple 0
                    push false
                    tuple 2
                }
                export function tau_reduce {
                    drop 0
                    push 1
                    push true
                    tuple 2
                }
                export function process {
                    untuple 2
                    drop 1
                }
                export function is_done {
                    drop 0
                    push false
                }
                export function is_ready_to_finish {
                    drop 0
                    push false
                }
            }

            export sentence test_no_tau {
                tuple 0
                jump m_no_tau::init
                jump m_no_tau::tau_reduce
            }

            export sentence test_with_tau {
                tuple 0
                jump m_with_tau::init
                jump m_with_tau::tau_reduce
            }
        "#;
        let res = bytecode::assemble(code).unwrap();

        // A machine with nothing to reduce says so and leaves its state alone.
        let idx = *res.exports.get("test_no_tau").unwrap();
        let mut vm = VM::new(res.clone());
        vm.execute(idx).expect("test_no_tau");
        assert_eq!(
            vm.stack(),
            &[Value::Tuple(vec![Value::Int(0), Value::Bool(false)])]
        );

        // One with a step to take hands back the state it stepped to.
        let idx = *res.exports.get("test_with_tau").unwrap();
        let mut vm = VM::new(res);
        vm.execute(idx).expect("test_with_tau");
        assert_eq!(
            vm.stack(),
            &[Value::Tuple(vec![Value::Int(1), Value::Bool(true)])]
        );
    }
}

/// The executable mirror of the junk table in `docs/totality.md`.
///
/// Every data instruction is total — it answers on every input — and answers
/// with one value of the type it computes, saying nothing about whether the
/// answer was computed or invented. These tests hold the VM to the table row by
/// row, so a row changed in one place and not the other is a failure rather
/// than a silent divergence.
#[cfg(test)]
mod totality_tests {
    use super::*;
    use bytecode::arity::op_arity;
    use bytecode::value::Symbol;

    /// Runs `body` on an empty stack and hands back what it left.
    fn run(body: Vec<Instruction>) -> Result<Vec<Value>, String> {
        let mut library = Library::new();
        library.sentences.push(body);
        let mut vm = VM::new(library);
        vm.execute(SentenceIndex::from(0))?;
        Ok(vm.stack().to_vec())
    }

    /// Pushes `operands` left to right, then runs `inst`.
    ///
    /// Panics if the instruction failed, which is the point: these are total,
    /// so `apply` having a `Result` would be admitting the thing under test.
    fn apply(operands: &[Value], inst: Instruction) -> Vec<Value> {
        let mut body: Vec<Instruction> = operands.iter().cloned().map(Instruction::Push).collect();
        body.push(inst.clone());
        run(body).unwrap_or_else(|e| panic!("{:?} on {:?} failed: {}", inst, operands, e))
    }

    /// A symbol, identified by its id — two are the same value exactly when
    /// their ids are, so the path is only there to print.
    fn sym(id: usize) -> Value {
        Value::Symbol(Symbol {
            id,
            path: format!("s{}", id),
        })
    }

    fn cs(text: &str) -> Value {
        Value::ConstString(text.to_string())
    }

    fn unit() -> Value {
        Value::Tuple(Vec::new())
    }

    /// One value of each shape, plus a couple of edge cases.
    fn every_shape() -> Vec<Value> {
        vec![
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(-3),
            // A second non-zero int, which is what it takes to tell an
            // operation that reads its operands in order from one that does
            // not: junk is the same `0` whichever way round the pair arrives,
            // so `6` against `-3` is the witness `0` against `-3` could not be.
            Value::Int(6),
            cs("hi"),
            cs(""),
            sym(7),
            unit(),
            Value::Tuple(vec![Value::Int(1), Value::Int(2)]),
            // A tuple holding a tuple, at the one width where taking it
            // apart hands back something that can be taken apart again:
            // without it `untuple 1` reads as its own answer, since every
            // other shape here coerces to the same one-slot junk.
            Value::Tuple(vec![Value::Tuple(vec![Value::Int(1)])]),
        ]
    }

    /// Every instruction that reads two operands, whether or not it commutes.
    ///
    /// The list is the *candidates*: the point of the sweep below is to find
    /// out which of them actually commute, rather than to restate a belief.
    fn every_binary() -> Vec<Instruction> {
        vec![
            Instruction::Equal,
            Instruction::Greater,
            Instruction::Less,
            Instruction::Add,
            Instruction::Subtract,
            Instruction::Multiply,
            Instruction::Divide,
            Instruction::Modulo,
            Instruction::And,
            Instruction::Or,
            Instruction::ConstStringCharAt,
            Instruction::Tuple(2),
        ]
    }

    /// Runs `a b op` and reports everything observable: the stack, or the
    /// failure.
    fn run_pair(a: &Value, b: &Value, inst: &Instruction) -> Result<Vec<Value>, String> {
        let mut library = Library::new();
        library.sentences.push(vec![
            Instruction::Push(a.clone()),
            Instruction::Push(b.clone()),
            inst.clone(),
        ]);
        let mut vm = VM::new(library);
        vm.execute(SentenceIndex::from(0))?;
        Ok(vm.stack().to_vec())
    }

    /// `Instruction::commutative` is measured, not asserted.
    ///
    /// Rewriting `roll 1 ; op` to `op` rests on that list, so a wrong entry
    /// would be a soundness bug in whatever reads it rather than an inaccuracy
    /// in a comment. This runs every candidate on every pair of shapes both
    /// ways round and holds the list to what it finds.
    #[test]
    fn the_commutative_instructions_are_exactly_the_ones_the_list_names() {
        for inst in every_binary() {
            let mut commutes = true;
            let mut witness = None;
            for a in every_shape() {
                for b in every_shape() {
                    if run_pair(&a, &b, &inst) != run_pair(&b, &a, &inst) {
                        commutes = false;
                        witness = Some((a.clone(), b.clone()));
                    }
                }
            }
            assert_eq!(
                commutes,
                inst.commutative(),
                "{:?} commutes = {}, but the list says {} (witness {:?})",
                inst,
                commutes,
                inst.commutative(),
                witness
            );
        }
    }

    /// Every instruction that reads one operand and leaves one.
    ///
    /// The candidates for the idempotence sweep, and like [`every_binary`]
    /// it is a list of questions rather than a list of answers: `not` and
    /// `negate` are their own inverses, `tuple 1` wraps whatever it is
    /// handed, and each `is_` test asked of its own answer asks about a
    /// `Bool` — five negative cases, so a sweep that passed on any list at
    /// all would be caught here.
    ///
    /// [`every_binary`]: every_binary
    fn every_unary() -> Vec<Instruction> {
        vec![
            Instruction::Not,
            Instruction::Negate,
            Instruction::ConstStringLen,
            Instruction::IsInt,
            Instruction::IsBool,
            Instruction::IsConstString,
            Instruction::IsSymbol,
            Instruction::IsTuple(None),
            Instruction::IsTuple(Some(2)),
            Instruction::TupleLength,
            Instruction::Tuple(1),
            Instruction::Untuple(1),
            Instruction::AsBool,
            Instruction::AsInt,
            // Both a width `every_shape` supplies a matching tuple for and
            // one it does not, so the sweep sees the coercion where it is
            // the identity and where it invents a value.
            Instruction::AsTuple(1),
            Instruction::AsTuple(2),
        ]
    }

    /// Runs `a` and then `inst` repeated `times`, and reports the stack.
    fn run_repeated(a: &Value, inst: &Instruction, times: usize) -> Result<Vec<Value>, String> {
        let mut library = Library::new();
        let mut body = vec![Instruction::Push(a.clone())];
        for _ in 0..times {
            body.push(inst.clone());
        }
        library.sentences.push(body);
        let mut vm = VM::new(library);
        vm.execute(SentenceIndex::from(0))?;
        Ok(vm.stack().to_vec())
    }

    /// `Instruction::idempotent` is measured, not asserted.
    ///
    /// Collapsing `op ; op` to `op` rests on that list, so a wrong entry
    /// would be a soundness bug in whatever reads it rather than an
    /// inaccuracy in a comment. This runs every candidate once and twice on
    /// every shape of operand and holds the list to what it finds.
    #[test]
    fn the_idempotent_instructions_are_exactly_the_ones_the_list_names() {
        for inst in every_unary() {
            let mut idempotent = true;
            let mut witness = None;
            for a in every_shape() {
                if run_repeated(&a, &inst, 1) != run_repeated(&a, &inst, 2) {
                    idempotent = false;
                    witness = Some(a.clone());
                }
            }
            assert_eq!(
                idempotent,
                inst.idempotent(),
                "{:?} is idempotent = {}, but the list says {} (witness {:?})",
                inst,
                idempotent,
                inst.idempotent(),
                witness
            );
        }
    }

    /// Every instruction whose result is computed from operands.
    ///
    /// The candidates for the sweep below, not the answer to it. `tuple n` is
    /// in the list precisely because it is *not* one — a sweep with no negative
    /// case is a sweep that would pass on any list at all.
    ///
    /// `push`, `drop`, `pick` and `roll` are absent because what they leave
    /// came off the stack rather than out of the instruction, so running them
    /// on operands measures nothing about them.
    fn every_computation() -> Vec<Instruction> {
        vec![
            Instruction::Equal,
            Instruction::Greater,
            Instruction::Less,
            Instruction::Add,
            Instruction::Subtract,
            Instruction::Multiply,
            Instruction::Divide,
            Instruction::Modulo,
            Instruction::Not,
            Instruction::Negate,
            Instruction::And,
            Instruction::Or,
            Instruction::ConstStringLen,
            Instruction::ConstStringCharAt,
            Instruction::IsInt,
            Instruction::IsBool,
            Instruction::IsConstString,
            Instruction::IsSymbol,
            // Both readings of the one test, so the sweep measures the
            // width-blind question and the widthed one alike.
            Instruction::IsTuple(None),
            Instruction::IsTuple(Some(2)),
            Instruction::TupleLength,
            Instruction::Untuple(2),
            Instruction::Tuple(2),
            // `as_tuple 2` is here at the width `every_shape` supplies a
            // matching tuple for, so the sweep sees both of its cases.
            Instruction::AsBool,
            Instruction::AsInt,
            Instruction::AsTuple(2),
        ]
    }

    /// Runs `op` on a list of operands and reports the whole stack.
    fn run_on(operands: &[Value], inst: &Instruction) -> Result<Vec<Value>, String> {
        let mut library = Library::new();
        let mut body: Vec<Instruction> = operands.iter().cloned().map(Instruction::Push).collect();
        body.push(inst.clone());
        library.sentences.push(body);
        let mut vm = VM::new(library);
        vm.execute(SentenceIndex::from(0))?;
        Ok(vm.stack().to_vec())
    }

    /// `Instruction::yields_bool` is measured, not asserted.
    ///
    /// Folding `op ; is_bool` to `op ; drop ; push true` rests on that list.
    /// The fact cannot be derived by rewriting — a codomain is not something a
    /// case split can reach — so this is the only thing holding it to the
    /// machine.
    #[test]
    fn the_instructions_that_leave_a_bool_are_exactly_the_ones_the_list_names() {
        for inst in every_computation() {
            let (n, _) = bytecode::arity::op_arity(&inst)
                .unwrap_or_else(|| panic!("{:?} has no arity", inst));
            let operand_sets: Vec<Vec<Value>> = match n {
                1 => every_shape().into_iter().map(|a| vec![a]).collect(),
                2 => every_shape()
                    .into_iter()
                    .flat_map(|a| every_shape().into_iter().map(move |b| vec![a.clone(), b]))
                    .collect(),
                other => panic!(
                    "{:?} reads {} operands, which the sweep does not build",
                    inst, other
                ),
            };

            let mut always = true;
            let mut witness = None;
            for operands in operand_sets {
                let top = run_on(&operands, &inst)
                    .ok()
                    .and_then(|s| s.last().cloned());
                if !matches!(top, Some(Value::Bool(_))) {
                    always = false;
                    witness = Some((operands, top));
                }
            }
            assert_eq!(
                always,
                inst.yields_bool(),
                "{:?} leaves a bool = {}, but the list says {} (witness {:?})",
                inst,
                always,
                inst.yields_bool(),
                witness
            );
        }
    }

    /// Every instruction with an off-domain case, with operands that reach it
    /// and the junk it answers with.
    ///
    /// The junk is always the **default of the type the instruction computes**,
    /// which is what is left of the old table now that nothing reports: `Int 0`
    /// for a number, `false` for a comparison, `()` for each slot `untuple`
    /// fills. Nothing hands an operand back, because there is no longer a slot
    /// whose meaning would say whether it had.
    fn off_domain_cases() -> Vec<(Instruction, Vec<Value>, Vec<Value>)> {
        let zero = vec![Value::Int(0)];
        vec![
            (Instruction::Add, vec![sym(7), Value::Int(1)], zero.clone()),
            (
                Instruction::Subtract,
                vec![Value::Int(1), sym(7)],
                zero.clone(),
            ),
            (
                Instruction::Multiply,
                vec![Value::Bool(true), Value::Bool(false)],
                zero.clone(),
            ),
            (
                Instruction::Divide,
                vec![Value::Int(7), Value::Int(0)],
                zero.clone(),
            ),
            (
                Instruction::Modulo,
                vec![Value::Int(7), Value::Int(0)],
                zero.clone(),
            ),
            (Instruction::Negate, vec![sym(7)], zero.clone()),
            (
                Instruction::Greater,
                vec![sym(1), sym(2)],
                vec![Value::Bool(false)],
            ),
            (
                Instruction::Less,
                vec![unit(), unit()],
                vec![Value::Bool(false)],
            ),
            (
                Instruction::Untuple(3),
                vec![Value::Int(5)],
                vec![unit(), unit(), unit()],
            ),
            // At width zero there is nothing to fill, and `untuple 0` takes its
            // argument whether or not the argument was `()`.
            (Instruction::Untuple(0), vec![Value::Int(5)], vec![]),
            (Instruction::TupleLength, vec![sym(7)], zero.clone()),
            (
                Instruction::ConstStringLen,
                vec![Value::Int(3)],
                zero.clone(),
            ),
            (
                Instruction::ConstStringCharAt,
                vec![cs("hi"), Value::Int(9)],
                zero,
            ),
        ]
    }

    // -- The shape of the contract ------------------------------------------

    #[test]
    fn an_instruction_keeps_its_arity_wherever_its_operands_land() {
        // A caller's stack does not depend on the data, which is why junk is
        // padding rather than an outcome: the arity checker works on shape
        // alone, and every rule that moves code past an instruction reads one
        // pair of numbers rather than reasoning about which case it hit.
        for (inst, bad, _) in off_domain_cases() {
            let (_, n_out) = op_arity(&inst).expect("a data instruction has a local arity");
            let out = apply(&bad, inst.clone());
            assert_eq!(
                out.len() as i64,
                n_out,
                "{:?} on {:?} left {} values, not {}",
                inst,
                bad,
                out.len(),
                n_out
            );
        }
    }

    #[test]
    fn off_its_domain_an_instruction_answers_with_the_default_of_its_type() {
        for (inst, bad, want) in off_domain_cases() {
            assert_eq!(apply(&bad, inst.clone()), want, "{:?} on {:?}", inst, bad);
        }
    }

    #[test]
    fn on_its_domain_it_answers_with_what_it_computed_and_nothing_else() {
        let cases: Vec<(Instruction, Vec<Value>, Vec<Value>)> = vec![
            (
                Instruction::Add,
                vec![Value::Int(1), Value::Int(2)],
                vec![Value::Int(3)],
            ),
            (
                Instruction::Divide,
                vec![Value::Int(7), Value::Int(2)],
                vec![Value::Int(3)],
            ),
            (
                Instruction::Negate,
                vec![Value::Int(3)],
                vec![Value::Int(-3)],
            ),
            (
                Instruction::Greater,
                vec![Value::Int(3), Value::Int(1)],
                vec![Value::Bool(true)],
            ),
            (
                Instruction::Untuple(2),
                vec![Value::Tuple(vec![sym(1), sym(2)])],
                vec![sym(1), sym(2)],
            ),
            (
                Instruction::TupleLength,
                vec![Value::Tuple(vec![Value::Int(1)])],
                vec![Value::Int(1)],
            ),
            (
                Instruction::ConstStringLen,
                vec![cs("hi")],
                vec![Value::Int(2)],
            ),
            (
                Instruction::ConstStringCharAt,
                vec![cs("hi"), Value::Int(0)],
                vec![Value::Int('h' as i64)],
            ),
        ];
        for (inst, good, want) in cases {
            assert_eq!(apply(&good, inst.clone()), want, "{:?} on {:?}", inst, good);
        }
    }

    #[test]
    fn untupling_is_coercing_and_then_taking_apart() {
        // The whole definition of the junk case, and the reason there is
        // nothing left to report: `untuple n` is `as_tuple n ; untuple n`, so
        // a caller that wants to know which case it is in asks `as_tuple` the
        // same question, on a copy, before handing the value over.
        for x in every_shape() {
            for n in 0..4 {
                let one = std::slice::from_ref(&x);
                assert_eq!(
                    apply(one, Instruction::Untuple(n)),
                    run(vec![
                        Instruction::Push(x.clone()),
                        Instruction::AsTuple(n),
                        Instruction::Untuple(n),
                    ])
                    .unwrap(),
                    "untuple {} of {:?}",
                    n,
                    x
                );
            }
        }
    }

    #[test]
    fn a_caller_that_wants_the_question_asked_can_ask_it() {
        // `pick 0 ; pick 0 ; as_tuple n ; equal` is the check it used to
        // make for everyone: true exactly where `untuple n` takes the value
        // apart rather than replacing it, and it leaves the value untouched
        // for the arm that answers `false`.
        for x in every_shape() {
            let asked = run(vec![
                Instruction::Push(x.clone()),
                Instruction::Copy,
                Instruction::Copy,
                Instruction::AsTuple(3),
                Instruction::Equal,
            ])
            .unwrap();
            let is_triple = matches!(&x, Value::Tuple(elements) if elements.len() == 3);
            assert_eq!(
                asked,
                vec![x.clone(), Value::Bool(is_triple)],
                "the check on {:?}",
                x
            );

            // And where it says yes, `tuple 3` puts back exactly what came
            // apart, which is the whole of what asking first is worth.
            if is_triple {
                assert_eq!(
                    run(vec![
                        Instruction::Push(x.clone()),
                        Instruction::Untuple(3),
                        Instruction::Tuple(3),
                    ])
                    .unwrap(),
                    vec![x.clone()],
                    "rebuild of {:?}",
                    x
                );
            }
        }
    }

    // -- The coercions ------------------------------------------------------

    /// The three coercions, each with the width the sweep has a value for.
    fn every_coercion() -> Vec<Instruction> {
        vec![
            Instruction::AsBool,
            Instruction::AsInt,
            Instruction::AsTuple(2),
        ]
    }

    /// Whether the value is one a coercion would leave alone.
    fn already(inst: &Instruction, v: &Value) -> bool {
        match (inst, v) {
            (Instruction::AsBool, Value::Bool(_)) => true,
            (Instruction::AsInt, Value::Int(_)) => true,
            (Instruction::AsTuple(n), Value::Tuple(elements)) => elements.len() == *n,
            _ => false,
        }
    }

    #[test]
    fn a_coercion_leaves_a_value_of_its_own_type_alone() {
        for inst in every_coercion() {
            for v in every_shape() {
                if already(&inst, &v) {
                    assert_eq!(
                        apply(std::slice::from_ref(&v), inst.clone()),
                        vec![v.clone()],
                        "{:?} should be the identity on {:?}",
                        inst,
                        v
                    );
                }
            }
        }
    }

    #[test]
    fn a_coercion_off_its_type_hands_back_the_default() {
        assert_eq!(apply(&[sym(7)], Instruction::AsInt), vec![Value::Int(0)]);
        assert_eq!(apply(&[cs("hi")], Instruction::AsInt), vec![Value::Int(0)]);
        assert_eq!(
            apply(&[Value::Int(3)], Instruction::AsTuple(2)),
            vec![Value::Tuple(vec![unit(), unit()])]
        );
        // A tuple of the wrong width is a mismatch like any other: it is
        // exactly what `untuple 2` could not have taken apart.
        assert_eq!(
            apply(
                &[Value::Tuple(vec![Value::Int(1)])],
                Instruction::AsTuple(2)
            ),
            vec![Value::Tuple(vec![unit(), unit()])]
        );
        // At width zero the only tuple that matches is the empty one, and the
        // default is that same empty tuple.
        assert_eq!(apply(&[sym(7)], Instruction::AsTuple(0)), vec![unit()]);
    }

    #[test]
    fn as_bool_is_the_truthiness_every_other_boolean_operation_applies() {
        for v in every_shape() {
            assert_eq!(
                apply(std::slice::from_ref(&v), Instruction::AsBool),
                vec![Value::Bool(v.truthy())],
                "as_bool {:?}",
                v
            );
            // Which is to say it is `not ; not`, the coercion spelled the long
            // way round.
            assert_eq!(
                run(vec![Instruction::Push(v.clone()), Instruction::AsBool]).unwrap(),
                run(vec![
                    Instruction::Push(v.clone()),
                    Instruction::Not,
                    Instruction::Not
                ])
                .unwrap(),
                "as_bool {:?} should be not ; not",
                v
            );
        }
    }

    /// The property the coercions exist for: what comes out is of the type
    /// named, whatever went in.
    ///
    /// A codomain is not something a rewrite can discover — case-splitting a
    /// value on `is_int` leaves it opaque in the arm where it is not one — so
    /// it has to be measured against the machine, exactly as `yields_bool` is.
    #[test]
    fn a_coercion_lands_in_the_type_it_names() {
        for v in every_shape() {
            let one = std::slice::from_ref(&v);
            assert!(matches!(
                apply(one, Instruction::AsBool)[..],
                [Value::Bool(_)]
            ));
            assert!(matches!(
                apply(one, Instruction::AsInt)[..],
                [Value::Int(_)]
            ));
            for n in 0..3 {
                match &apply(one, Instruction::AsTuple(n))[..] {
                    [Value::Tuple(elements)] => assert_eq!(elements.len(), n),
                    other => panic!("as_tuple {} left {:?} on {:?}", n, other, v),
                }
            }
        }
    }

    #[test]
    fn a_coercion_is_idempotent() {
        for inst in every_coercion() {
            for v in every_shape() {
                let once = run(vec![Instruction::Push(v.clone()), inst.clone()]).unwrap();
                let twice = run(vec![
                    Instruction::Push(v.clone()),
                    inst.clone(),
                    inst.clone(),
                ])
                .unwrap();
                assert_eq!(once, twice, "{:?} twice on {:?}", inst, v);
            }
        }
    }

    /// Two consequences of the codomain, which are what makes a coercion worth
    /// writing rather than a check worth reading.
    #[test]
    fn a_coercion_settles_the_question_that_follows_it() {
        for v in every_shape() {
            // `as_int ; is_int` is `drop ; push true`.
            assert_eq!(
                run(vec![
                    Instruction::Push(v.clone()),
                    Instruction::AsInt,
                    Instruction::IsInt
                ])
                .unwrap(),
                vec![Value::Bool(true)],
                "as_int ; is_int on {:?}",
                v
            );
            // `as_tuple n ; untuple n ; tuple n` is `as_tuple n`: after the
            // coercion the taking apart is exact, junk or not.
            assert_eq!(
                run(vec![
                    Instruction::Push(v.clone()),
                    Instruction::AsTuple(2),
                    Instruction::Untuple(2),
                    Instruction::Tuple(2),
                ])
                .unwrap(),
                run(vec![Instruction::Push(v.clone()), Instruction::AsTuple(2)]).unwrap(),
                "as_tuple 2 ; untuple 2 should come apart exactly, on {:?}",
                v
            );
        }
    }

    // -- The instructions with no domain to be off --------------------------

    #[test]
    fn only_bool_false_is_false() {
        for v in every_shape() {
            let expected = v != Value::Bool(false);
            assert_eq!(
                apply(std::slice::from_ref(&v), Instruction::Not),
                vec![Value::Bool(!expected)],
                "not {:?}",
                v
            );
        }
        // Junk is not `false`, so it is true and its negation is `false`.
        assert_eq!(
            apply(&[Value::Int(42)], Instruction::Not),
            vec![Value::Bool(false)]
        );
        assert_eq!(
            apply(&[Value::unit()], Instruction::Not),
            vec![Value::Bool(false)]
        );
    }

    #[test]
    fn and_and_or_coerce_each_operand_separately() {
        for a in every_shape() {
            for b in every_shape() {
                let (p, q) = (a != Value::Bool(false), b != Value::Bool(false));
                assert_eq!(
                    apply(&[a.clone(), b.clone()], Instruction::And),
                    vec![Value::Bool(p && q)],
                    "{:?} and {:?}",
                    a,
                    b
                );
                assert_eq!(
                    apply(&[a.clone(), b.clone()], Instruction::Or),
                    vec![Value::Bool(p || q)],
                    "{:?} or {:?}",
                    a,
                    b
                );
            }
        }
    }

    #[test]
    fn de_morgan_holds_on_every_value() {
        // What per-operand coercion is for: there is no input `and`, `or` or
        // `not` cannot answer on, so none of them has junk to answer with.
        for a in every_shape() {
            for b in every_shape() {
                let lhs = run(vec![
                    Instruction::Push(a.clone()),
                    Instruction::Push(b.clone()),
                    Instruction::And,
                    Instruction::Not,
                ])
                .unwrap();
                let rhs = run(vec![
                    Instruction::Push(a.clone()),
                    Instruction::Not,
                    Instruction::Push(b.clone()),
                    Instruction::Not,
                    Instruction::Or,
                ])
                .unwrap();
                assert_eq!(lhs, rhs, "de Morgan on {:?}, {:?}", a, b);
            }
        }
    }

    #[test]
    fn a_branch_takes_the_then_arm_on_anything_but_false() {
        for v in every_shape() {
            let mut library = Library::new();
            library.sentences.push(vec![
                Instruction::Push(v.clone()),
                Instruction::Branch(SentenceIndex::from(1), SentenceIndex::from(2)),
            ]);
            library
                .sentences
                .push(vec![Instruction::Push(Value::Int(1))]);
            library
                .sentences
                .push(vec![Instruction::Push(Value::Int(2))]);

            let mut vm = VM::new(library);
            vm.execute(SentenceIndex::from(0))
                .unwrap_or_else(|e| panic!("branch on {:?} failed: {}", v, e));
            let taken = if v != Value::Bool(false) { 1 } else { 2 };
            assert_eq!(vm.stack(), &[Value::Int(taken)], "branch on {:?}", v);
        }
    }

    #[test]
    fn equality_and_the_type_tests_answer_on_every_pair() {
        for a in every_shape() {
            for b in every_shape() {
                assert_eq!(
                    apply(&[a.clone(), b.clone()], Instruction::Equal),
                    vec![Value::Bool(a == b)],
                    "{:?} == {:?}",
                    a,
                    b
                );
            }
            for (inst, want) in [
                (Instruction::IsInt, matches!(a, Value::Int(_))),
                (Instruction::IsBool, matches!(a, Value::Bool(_))),
                (
                    Instruction::IsConstString,
                    matches!(a, Value::ConstString(_)),
                ),
                (Instruction::IsSymbol, matches!(a, Value::Symbol(_))),
                (Instruction::IsTuple(None), matches!(a, Value::Tuple(_))),
                // The width is the whole question: a tuple of the wrong
                // length answers no, the same no a symbol answers.
                (
                    Instruction::IsTuple(Some(0)),
                    matches!(&a, Value::Tuple(t) if t.is_empty()),
                ),
                (
                    Instruction::IsTuple(Some(2)),
                    matches!(&a, Value::Tuple(t) if t.len() == 2),
                ),
            ] {
                assert_eq!(
                    apply(std::slice::from_ref(&a), inst.clone()),
                    vec![Value::Bool(want)],
                    "{:?} of {:?}",
                    inst,
                    a
                );
            }
        }
    }

    // -- Numbers ------------------------------------------------------------

    #[test]
    fn division_by_zero_answers_zero_like_anything_else_off_the_domain() {
        // `int` is the whole of arithmetic, so a zero divisor has no quotient
        // to give and takes the default an `Int` slot takes everywhere. A
        // caller that means to tell the two apart tests the divisor.
        assert_eq!(
            apply(&[Value::Int(1), Value::Int(0)], Instruction::Divide),
            vec![Value::Int(0)]
        );
        assert_eq!(
            apply(&[Value::Int(1), Value::Int(0)], Instruction::Modulo),
            vec![Value::Int(0)]
        );
    }

    #[test]
    fn integer_arithmetic_wraps_rather_than_overflowing_the_host() {
        assert_eq!(
            apply(&[Value::Int(i64::MIN), Value::Int(-1)], Instruction::Divide),
            vec![Value::Int(i64::MIN)]
        );
        assert_eq!(
            apply(&[Value::Int(i64::MIN), Value::Int(-1)], Instruction::Modulo),
            vec![Value::Int(0)]
        );
    }

    #[test]
    fn comparisons_answer_on_two_ints_and_answer_false_off_the_numbers() {
        assert_eq!(
            apply(&[Value::Int(1), Value::Int(2)], Instruction::Less),
            vec![Value::Bool(true)]
        );
        // Anything that is not a pair of ints is not a comparison, and `false`
        // is what it says about an ordering that does not hold either. The two
        // are the same answer on purpose: a caller that needs them apart asks
        // `is_int` before it compares.
        assert_eq!(
            apply(&[cs("a"), Value::Int(1)], Instruction::Less),
            vec![Value::Bool(false)]
        );
        assert_eq!(
            apply(&[Value::Int(2), Value::Int(1)], Instruction::Less),
            vec![Value::Bool(false)]
        );
    }

    // -- What is still an error ---------------------------------------------

    #[test]
    fn underflow_is_still_an_error_because_it_is_structural() {
        // The only way a run can still end early, and it is structural rather
        // than about values: ruled out by arity checking, so a sentence that
        // would underflow does not assemble in the first place.
        for body in [
            vec![Instruction::Drop],
            vec![Instruction::Copy],
            vec![Instruction::Swap],
            vec![Instruction::Tuple(1)],
            vec![Instruction::Add],
        ] {
            assert!(
                run(body.clone()).is_err(),
                "{:?} on an empty stack should underflow",
                body
            );
        }
    }
}

#[cfg(test)]
mod runtime_tests {
    use super::*;
    use bytecode::assemble;
    use bytecode::value::Symbol;

    struct TestEnv {
        pong_symbol: Symbol,
        received_ping: bool,
    }

    impl Environment for TestEnv {
        async fn handle_event(&mut self, event: Value) -> Result<(), String> {
            match event {
                Value::Symbol(sym) => {
                    if sym.path == "main::event::ping" {
                        self.received_ping = true;
                        return Ok(());
                    }
                    Err(format!("Unexpected symbol event: {}", sym.path))
                }
                other => Err(format!("Unexpected event type: {:?}", other)),
            }
        }

        async fn wait_for_event(&mut self) -> Result<Value, String> {
            if !self.received_ping {
                return Err("wait_for_event called before ping!".to_string());
            }
            Ok(Value::Symbol(self.pong_symbol.clone()))
        }
    }

    #[tokio::test]
    async fn test_runtime_ping_pong() {
        let code = r#"
            mod main {
                mod state {
                    symbol init
                    symbol waiting
                    symbol done
                }

                mod event {
                    symbol ping
                    symbol pong
                }

                export function init {
                    // `untuple 0` takes the argument either way, which is the
                    // whole of what it does.
                    untuple 0
                    push state::init
                }

                export sentence accept {
                    // A malformed event untuples to a pair of `()`s, which
                    // matches no state and so is declined below.
                    untuple 2
                    // Stack: [event, state]
                    push state::waiting
                    equal
                    branch {
                        push event::pong
                        equal
                    } {
                        drop 0
                        push false
                    }
                }

                export function tau_reduce {
                    push false
                    tuple 2
                }

                export function emit {
                    push state::init
                    equal
                    branch {
                        push event::ping
                        push true
                        tuple 2
                    } {
                        tuple 0
                        push false
                        tuple 2
                    }
                }

                export function process {
                    untuple 2
                    // Stack: [event, state]
                    pick 0
                    push state::init
                    equal
                    branch {
                        // In `init`, a ping is what moves us on. Anything
                        // else — including a malformed event — leaves the
                        // state where it was.
                        drop 0
                        push event::ping
                        equal
                        branch {
                            push state::waiting
                        } {
                            push state::init
                        }
                    } {
                        // Stack: [event, state]
                        roll 1
                        push event::pong
                        equal
                        branch {
                            drop 0
                            push state::done
                        } {
                        }
                    }
                }

                export function is_done {
                    push state::done
                    equal
                }

                export function is_ready_to_finish {
                    drop 0
                    push false
                }
            }
        "#;

        let res = assemble(code).unwrap();
        let pong_symbol = res
            .symbols
            .get("main::event::pong")
            .cloned()
            .and_then(|v| match v {
                Value::Symbol(s) => Some(s),
                _ => None,
            })
            .unwrap();
        let env = TestEnv {
            pong_symbol,
            received_ping: false,
        };
        let mut runtime = Runtime::new(res, "main", env).unwrap();

        let run_res = runtime.run().await;
        if let Err(ref e) = run_res {
            println!("Runtime run failed: {}", e);
        }
        assert!(run_res.is_ok());
        assert!(runtime.environment.received_ping);
    }

    #[tokio::test]
    async fn test_runtime_hello_world() {
        let code = r#"
            mod std {
                mod io {
                    symbol io
                    mod stdout {
                        symbol stdout
                        symbol putch
                    }
                }
            }

            mod main {
                const_string hello "Hello, World!"

                export function init {
                    // `untuple 0` takes the argument either way, which is the
                    // whole of what it does.
                    untuple 0
                    push 0
                }

                export sentence accept {
                    // This machine only writes, so nothing is accepted and
                    // the shape of the event never comes up.
                    untuple 2
                    drop 0
                    drop 0
                    push false
                }

                export function tau_reduce {
                    push false
                    tuple 2
                }

                export function emit {
                    pick 0
                    push hello
                    const_string_len
                    less
                    branch {
                        push ()

                        push hello
                        pick 2 // index
                        const_string_char_at
                        // In range, since `less` is what got us into this arm.

                        tuple 2 // ((), char)
                        
                        push crate::std::io::stdout::putch
                        tuple 2 // (((), char), putch)
                        
                        push crate::std::io::stdout::stdout
                        tuple 2 // ((((), char), putch), stdout)
                        
                        push crate::std::io::io
                        tuple 2 // (((((), char), putch), stdout), io)
                        
                        // Stack is [index, event]
                        // We swap to [event, index], drop index, then push true and wrap
                        roll 1
                        drop 0
                        push true
                        tuple 2
                    } {
                        drop 0
                        tuple 0
                        push false
                        tuple 2
                    }
                }

                export function process {
                    untuple 2
                    drop 1 // drop event
                    push 1
                    add
                }

                export function is_done {
                    push hello
                    const_string_len
                    less
                    not
                }

                export function is_ready_to_finish {
                    drop 0
                    push false
                }
            }
        "#;

        let res = assemble(code).unwrap();
        let env = DefaultEnvironment::with_capture(&res);
        let mut runtime = Runtime::new(res, "main", env).unwrap();

        let run_res = runtime.run().await;
        if let Err(ref e) = run_res {
            println!("Hello world run failed: {}", e);
        }
        assert!(run_res.is_ok());

        let output = runtime.environment.captured_output().unwrap();
        assert_eq!(output, "Hello, World!");
    }
}

/// What the movement macros mean, measured against the machine.
///
/// `pick d`, `roll d` and `drop d` are not instructions: phase 4 expands each
/// into frames around `copy`, `swap` and `drop`, and a program never sees the
/// depth again. What that expansion is *supposed* to compute is the indexed
/// operation it replaced — copy the value at depth `d` to the top, move it to
/// the top, discard it — and the expansion being right is a claim about the
/// compiler that nothing in the compiler can check.
///
/// So it is measured, the way [`Instruction::commutative`] and
/// [`Instruction::yields_bool`] are: both sides are run and compared, over
/// every depth and every stack size the sweep reaches. A wrong recursion is a
/// silently wrong program, and this is what stands between the two.
#[cfg(test)]
mod movement_tests {
    use crate::VM;
    use bytecode::{Value, assemble};

    /// The deepest reach the sweep goes to. The corpus's deepest is `pick 5`;
    /// this covers past it, and the expansion is a recursion, so a depth that
    /// works at seven works at seventy.
    const DEEPEST: usize = 7;

    /// Runs `body` over a stack of `size` distinct ints and hands back what it
    /// left, bottom first.
    ///
    /// The values are `0 … size-1`, all different, so a permutation that went
    /// wrong cannot pass by coincidence.
    fn run(size: usize, body: &str) -> Vec<Value> {
        let pushes: String = (0..size).map(|i| format!("push {} ", i)).collect();
        let src = format!("export sentence probe {{ {}{} }}", pushes, body);
        let lib = assemble(&src).unwrap_or_else(|e| panic!("`{}` did not assemble: {}", body, e));
        let idx = *lib.exports.get("probe").unwrap();
        let mut vm = VM::new(lib);
        vm.execute(idx)
            .unwrap_or_else(|e| panic!("`{}` did not run: {}", body, e));
        vm.stack().to_vec()
    }

    fn ints(values: &[i64]) -> Vec<Value> {
        values.iter().map(|v| Value::Int(*v)).collect()
    }

    /// `pick d` leaves the stack alone and puts a copy of its `d`th value on
    /// top, counting from the top at zero.
    #[test]
    fn pick_copies_the_value_at_that_depth_to_the_top() {
        for d in 0..DEEPEST {
            for extra in 0..3 {
                let size = d + 1 + extra;
                let mut want: Vec<i64> = (0..size as i64).collect();
                want.push(want[size - 1 - d]);
                assert_eq!(
                    run(size, &format!("pick {}", d)),
                    ints(&want),
                    "pick {} on a stack of {}",
                    d,
                    size
                );
            }
        }
    }

    /// `roll d` lifts its `d`th value to the top, shifting the rest down.
    #[test]
    fn roll_moves_the_value_at_that_depth_to_the_top() {
        for d in 0..DEEPEST {
            for extra in 0..3 {
                let size = d + 1 + extra;
                let mut want: Vec<i64> = (0..size as i64).collect();
                let moved = want.remove(size - 1 - d);
                want.push(moved);
                assert_eq!(
                    run(size, &format!("roll {}", d)),
                    ints(&want),
                    "roll {} on a stack of {}",
                    d,
                    size
                );
            }
        }
    }

    /// `drop d` removes its `d`th value and shifts the rest down.
    #[test]
    fn drop_discards_the_value_at_that_depth() {
        for d in 0..DEEPEST {
            for extra in 0..3 {
                let size = d + 1 + extra;
                let mut want: Vec<i64> = (0..size as i64).collect();
                want.remove(size - 1 - d);
                assert_eq!(
                    run(size, &format!("drop {}", d)),
                    ints(&want),
                    "drop {} on a stack of {}",
                    d,
                    size
                );
            }
        }
    }

    /// `dip N { X }` hides the top `N` values from `X` and puts them back.
    ///
    /// The width is no longer on the instruction — `dip 3` is three frames —
    /// so what is measured here is that the nesting hides what the width used
    /// to name, and in the same order.
    #[test]
    fn a_nest_of_frames_hides_what_a_width_named() {
        for n in 0..DEEPEST {
            let size = n + 2;
            let mut want: Vec<i64> = (0..size as i64).collect();
            // The block replaces the two values under the hidden region with
            // one, which is the arity that makes the restore observable.
            want.splice(size - n - 2..size - n, [99]);
            assert_eq!(
                run(size, &format!("dip {} {{ add drop 0 push 99 }}", n)),
                ints(&want),
                "dip {} left the hidden values wrong",
                n
            );
        }
    }

    /// The two spellings of a copy at depth agree: `pick d` is a copy made
    /// under the frame and rolled up.
    ///
    /// This used to be an axiom stated about the instruction set. It is now the
    /// compiler's own definition read at one remove, and the sweep keeps the
    /// two spellings honest about being one thing.
    #[test]
    fn copying_from_depth_is_copying_at_depth_and_rolling_up() {
        for d in 0..DEEPEST {
            for extra in 0..3 {
                let size = d + 1 + extra;
                assert_eq!(
                    run(size, &format!("pick {}", d)),
                    run(size, &format!("dip {} {{ pick 0 }} roll {}", d, d)),
                    "pick {} is not the framed copy rolled up, on a stack of {}",
                    d,
                    size
                );
            }
        }
    }

    /// `(roll d)^(d+1)` = nothing: a rotation of `d+1` things has order `d+1`.
    ///
    /// This used to be an axiom stated for every `d`. All that needs assuming
    /// now is the `d = 1` case, `swap ; swap` = nothing, and every other depth
    /// is a consequence of the expansion — so the sweep is what says the
    /// consequence really follows.
    #[test]
    fn rolling_the_whole_way_round_is_the_identity() {
        for d in 0..DEEPEST {
            for extra in 0..3 {
                let size = d + 1 + extra;
                let cycle = format!("roll {} ", d).repeat(d + 1);
                assert_eq!(
                    run(size, &cycle),
                    run(size, ""),
                    "(roll {})^{} moved something, on a stack of {}",
                    d,
                    d + 1,
                    size
                );
            }
        }
    }

    /// `dip d { X } ; (roll (d+m-1))^m` = `(roll (d+n-1))^n ; X`, for `X : n -> m`.
    ///
    /// A framed computation is a rolled one — the law that brings a value out
    /// from under a frame to where the folding equations can read it.
    #[test]
    fn a_framed_computation_is_a_rolled_one() {
        // Each body with the arity it has, since the law counts both.
        let bodies: [(&str, usize, usize); 6] = [
            ("is_symbol", 1, 1),
            ("not", 1, 1),
            ("push true", 0, 1),
            ("add", 2, 1),
            ("and", 2, 1),
            ("drop 0", 1, 0),
        ];
        for (body, n, m) in bodies {
            for d in 0..5 {
                for extra in 0..2 {
                    let size = d + n + extra;
                    let lhs = format!(
                        "dip {} {{ {} }} {}",
                        d,
                        body,
                        format!("roll {} ", d + m.saturating_sub(1)).repeat(m)
                    );
                    let rhs = format!(
                        "{}{}",
                        format!("roll {} ", d + n.saturating_sub(1)).repeat(n),
                        body
                    );
                    assert_eq!(
                        run(size, &lhs),
                        run(size, &rhs),
                        "dip {} {{ {} }} is not the rolled form, on a stack of {}",
                        d,
                        body,
                        size
                    );
                }
            }
        }
    }
}
