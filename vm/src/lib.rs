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

    /// A fallible instruction that computed its answer: the value, then `true`.
    fn ok(&mut self, value: Value) {
        self.stack.push(value);
        self.stack.push(Value::Bool(true));
    }

    /// A fallible instruction that did not: junk, then `false`.
    ///
    /// The caller passes whatever fills the result slots, which is where the
    /// "preserve the inputs" rule of `docs/totality.md` is applied — an
    /// instruction whose output arity has room hands its own input back, and
    /// one whose does not fills with a default.
    fn failed(&mut self, value: Value) {
        self.stack.push(value);
        self.stack.push(Value::Bool(false));
    }

    /// [`failed`](Self::failed) with several result slots to fill.
    fn failed_with(&mut self, values: impl IntoIterator<Item = Value>) {
        self.stack.extend(values);
        self.stack.push(Value::Bool(false));
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
                Instruction::Pick(depth) => {
                    if self.stack.len() <= depth {
                        return Err(format!(
                            "Stack underflow on Pick: depth {} but stack size {}",
                            depth,
                            self.stack.len()
                        ));
                    }
                    let index = self.stack.len() - 1 - depth;
                    let val = self.stack[index].clone();
                    self.stack.push(val);
                }
                Instruction::Roll(depth) => {
                    if self.stack.len() <= depth {
                        return Err(format!(
                            "Stack underflow on Roll: depth {} but stack size {}",
                            depth,
                            self.stack.len()
                        ));
                    }
                    let index = self.stack.len() - 1 - depth;
                    let val = self.stack.remove(index);
                    self.stack.push(val);
                }
                Instruction::Equal => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(Value::Bool(a == b));
                }
                Instruction::Greater | Instruction::Less => {
                    // A NaN is unordered rather than non-numeric, but neither
                    // pair yields an ordering and neither is a comparison this
                    // instruction can claim to have made.
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let want = if matches!(instruction, Instruction::Greater) {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Less
                    };
                    match numeric_cmp(&a, &b) {
                        Some(ord) => self.ok(Value::Bool(ord == want)),
                        // Two slots and two inputs, so there is no room to keep
                        // them; the result slot takes the junk answer.
                        None => self.failed(Value::Bool(false)),
                    }
                }
                Instruction::Add => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    match (a, b) {
                        (Value::Int(x), Value::Int(y)) => self.ok(Value::Int(x.wrapping_add(y))),
                        _ => self.failed(Value::Int(0)),
                    }
                }
                Instruction::Subtract => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    match (a, b) {
                        (Value::Int(x), Value::Int(y)) => self.ok(Value::Int(x.wrapping_sub(y))),
                        _ => self.failed(Value::Int(0)),
                    }
                }
                Instruction::Multiply => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    match (a, b) {
                        (Value::Int(x), Value::Int(y)) => self.ok(Value::Int(x.wrapping_mul(y))),
                        _ => self.failed(Value::Int(0)),
                    }
                }
                Instruction::Divide => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    match (a, b) {
                        // Division by zero has no answer to report, and it
                        // says so rather than inventing one.
                        (Value::Int(_), Value::Int(0)) => self.failed(Value::Int(0)),
                        // `wrapping_div` keeps `i64::MIN / -1` from being a
                        // host-level overflow.
                        (Value::Int(x), Value::Int(y)) => self.ok(Value::Int(x.wrapping_div(y))),
                        _ => self.failed(Value::Int(0)),
                    }
                }
                Instruction::Modulo => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    match (a, b) {
                        (Value::Int(_), Value::Int(0)) => self.failed(Value::Int(0)),
                        (Value::Int(x), Value::Int(y)) => self.ok(Value::Int(x.wrapping_rem(y))),
                        _ => self.failed(Value::Int(0)),
                    }
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
                    // One input and two slots, so failure hands the value back.
                    let val = self.pop()?;
                    match val {
                        Value::Int(x) => self.ok(Value::Int(x.wrapping_neg())),
                        other => self.failed(other),
                    }
                }
                Instruction::Dip(depth, target) => {
                    if self.stack.len() < depth {
                        return Err(format!(
                            "Stack underflow on Dip: depth {} but stack size {}",
                            depth,
                            self.stack.len()
                        ));
                    }
                    // Withhold the top `depth` values for the duration of the call.
                    let hidden = self.stack.split_off(self.stack.len() - depth);
                    self.call_stack.push(Frame {
                        sentence: current_sentence,
                        ip,
                        hidden,
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
                Instruction::Panic => {
                    return Err("Panic instruction executed".to_string());
                }
                Instruction::Assert => {
                    // One of the three instructions that may still fail, and
                    // it fails on anything that is not `Bool(true)` — a
                    // non-boolean is a failed assertion rather than a
                    // separate kind of error.
                    let val = self.pop()?;
                    if !val.truthy() {
                        return Err(format!("Assertion failed: {:?} is not true", val));
                    }
                }
                Instruction::AssertEqual => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    if a != b {
                        return Err(format!(
                            "Assertion failed: values are not equal: {:?} != {:?}",
                            a, b
                        ));
                    }
                }
                Instruction::Tuple(n) => {
                    if self.stack.len() < n {
                        return Err(format!(
                            "Stack underflow on Tuple: requested {} but stack size {}",
                            n,
                            self.stack.len()
                        ));
                    }
                    let index = self.stack.len() - n;
                    let mut elements = self.stack.split_off(index);
                    elements.reverse();
                    self.stack.push(Value::Tuple(elements));
                }
                Instruction::Untuple(n) => {
                    // The instruction the "preserve the inputs" rule is really
                    // for. On failure the value stays in the slot it occupied
                    // and the n-1 slots above it take `()`, so a caller that
                    // reads the flag can drop the padding and still have its
                    // value — which is what makes the flag a tag on the *stack*
                    // rather than inside `Value`. See `docs/totality.md`.
                    let val = self.pop()?;
                    match val {
                        Value::Tuple(elements) if elements.len() == n => {
                            for elem in elements.into_iter().rev() {
                                self.stack.push(elem);
                            }
                            self.stack.push(Value::Bool(true));
                        }
                        // At n = 0 there is no room for the value, and nothing
                        // to hold it for: the flag is the whole answer.
                        _ if n == 0 => self.failed_with(std::iter::empty()),
                        other => {
                            let padding = std::iter::repeat_n(Value::unit(), n - 1);
                            self.failed_with(std::iter::once(other).chain(padding))
                        }
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
                Instruction::IsTuple => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(val, Value::Tuple(_))));
                }
                Instruction::TupleLength => {
                    // One input and two slots, so a non-tuple comes back out
                    // rather than being replaced by a length it does not have.
                    let val = self.pop()?;
                    match val {
                        Value::Tuple(elements) => self.ok(Value::Int(elements.len() as i64)),
                        other => self.failed(other),
                    }
                }
                Instruction::ConstStringLen => {
                    let val = self.pop()?;
                    match val {
                        Value::ConstString(ref s) => {
                            let len = s.chars().count() as i64;
                            self.ok(Value::Int(len))
                        }
                        other => self.failed(other),
                    }
                }
                Instruction::ConstStringCharAt => {
                    let idx_val = self.pop()?;
                    let str_val = self.pop()?;
                    // Wrong types and an out-of-range index fail alike: an index
                    // is in range or it is not, and there is nothing for a
                    // caller to learn from telling the two apart. Two inputs and
                    // two slots leave no room to hand either back.
                    let ch = match (str_val, idx_val) {
                        (Value::ConstString(s), Value::Int(idx)) => usize::try_from(idx)
                            .ok()
                            .and_then(|idx| s.chars().nth(idx))
                            .map(|ch| ch as i64),
                        _ => None,
                    };
                    match ch {
                        Some(ch) => self.ok(Value::Int(ch)),
                        None => self.failed(Value::Int(0)),
                    }
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
            // `add` is fallible, so this drops the flag it leaves. Source would
            // say `assert`; hand-written bytecode says what it means.
            Instruction::Drop,
            Instruction::Push(Value::Int(30)),
            Instruction::AssertEqual,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert!(vm.stack().is_empty()); // AssertEqual popped both
    }

    #[test]
    fn test_stack_manipulation() {
        let mut library = Library::new();
        let sentence = vec![
            Instruction::Push(Value::Int(5)),
            Instruction::Pick(0),     // Dup
            Instruction::AssertEqual, // pop both, check equal
            Instruction::Push(Value::Int(5)),
            Instruction::Push(Value::Int(10)),
            Instruction::Roll(1), // Swap top two
            Instruction::Push(Value::Int(5)),
            Instruction::AssertEqual,
            Instruction::Push(Value::Int(10)),
            Instruction::AssertEqual,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert!(vm.stack().is_empty());
    }

    #[test]
    fn test_branching() {
        let mut library = Library::new();

        // idx 0: Push true, Branch to idx 1, else idx 2 (which asserts false)
        // idx 1: Push 42, return (reaches end, returns to idx 0 which then reaches end and completes)
        // idx 2: Push false, Assert (panics)
        let s0 = vec![
            Instruction::Push(Value::Bool(true)),
            Instruction::Branch(SentenceIndex::from(1), SentenceIndex::from(2)),
        ];
        let s1 = vec![Instruction::Push(Value::Int(42))];
        let s2 = vec![Instruction::Push(Value::Bool(false)), Instruction::Assert];

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

        // sentence 0: Push 10, call sentence 1, then AssertEqual (verifying that sentence 1 ran and returned to s0)
        let s0 = vec![
            Instruction::Push(Value::Int(10)),
            Instruction::Dip(0, SentenceIndex::from(1)),
            Instruction::AssertEqual,
        ];

        // sentence 1: Push 10
        let s1 = vec![Instruction::Push(Value::Int(10))];

        library.sentences.push(s0);
        library.sentences.push(s1);

        let mut vm = VM::new(library);
        assert!(vm.execute(SentenceIndex::from(0)).is_ok());
        assert!(vm.stack().is_empty());
    }

    #[test]
    fn test_dip_hides_the_top_of_stack() {
        let mut library = Library::new();

        // sentence 0: [1, 2, 99], dip past 99 and add, expecting [3, 99].
        let s0 = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Push(Value::Int(99)),
            Instruction::Dip(1, SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Add, Instruction::Drop];

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
            Instruction::Dip(0, SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Add, Instruction::Drop];

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
            Instruction::Dip(1, SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Dip(1, SentenceIndex::from(2))];
        let s2 = vec![Instruction::Add, Instruction::Drop];

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

        let s0 = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Dip(3, SentenceIndex::from(1)),
        ];
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
        // push 1, push 2, push 3, tuple(3) -> Tuple(3, 2, 1)
        // untuple(3) -> pushes 1, 2, 3 back.
        let sentence = vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Push(Value::Int(3)),
            Instruction::Tuple(3),
            Instruction::Untuple(3),
            Instruction::Drop, // the untuple's success flag
            Instruction::Push(Value::Int(3)),
            Instruction::AssertEqual,
            Instruction::Push(Value::Int(2)),
            Instruction::AssertEqual,
            Instruction::Push(Value::Int(1)),
            Instruction::AssertEqual,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert!(vm.stack().is_empty());
    }

    #[test]
    fn test_type_checks_and_tuple_length() {
        let mut library = Library::new();
        let sentence = vec![
            // test is_int
            Instruction::Push(Value::Int(42)),
            Instruction::IsInt,
            Instruction::Push(Value::Bool(true)),
            Instruction::AssertEqual,
            Instruction::Push(Value::Bool(true)),
            Instruction::IsInt,
            Instruction::Push(Value::Bool(false)),
            Instruction::AssertEqual,
            // test is_bool
            Instruction::Push(Value::Bool(true)),
            Instruction::IsBool,
            Instruction::Push(Value::Bool(true)),
            Instruction::AssertEqual,
            // test is_tuple
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Tuple(2),
            Instruction::IsTuple,
            Instruction::Push(Value::Bool(true)),
            Instruction::AssertEqual,
            // test tuple_length
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::Tuple(2),
            Instruction::TupleLength,
            Instruction::Drop, // the tuple_length's success flag
            Instruction::Push(Value::Int(2)),
            Instruction::AssertEqual,
        ];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        assert!(vm.execute(idx).is_ok());
        assert!(vm.stack().is_empty());
    }

    #[test]
    fn test_assertion_failure() {
        let mut library = Library::new();
        let sentence = vec![Instruction::Push(Value::Bool(false)), Instruction::Assert];
        library.sentences.push(sentence);
        let idx = SentenceIndex::from(0);

        let mut vm = VM::new(library);
        let res = vm.execute(idx);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Assertion failed"));
    }

    #[test]
    fn test_integration_assembler_vm() {
        let code = r#"
            export sentence start {
                push 10
                push 20
                add
                assert
                push 30
                assert_eq
                
                // Test branching with inline targets
                push true
                branch {
                    push 100
                } {
                    panic
                }
                
                // Check that the branch returned and we continue here
                push 100
                assert_eq
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let start_idx = *res.exports.get("start").unwrap();

        let mut vm = VM::new(res);
        assert!(vm.execute(start_idx).is_ok());
        assert!(vm.stack().is_empty());
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
                assert
                
                // Compare it to status_error (should not be equal)
                push status_ok
                push status_error
                equal
                not
                assert
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let entry_idx = *res.exports.get("entry").unwrap();

        let mut vm = VM::new(res);
        assert!(vm.execute(entry_idx).is_ok());
        assert!(vm.stack().is_empty());
    }

    #[test]
    fn test_const_string_len_and_char_at() {
        let code = r#"
            const_string ascii_str "hello"
            const_string unicode_str "café"
            
            export sentence test_len {
                push ascii_str
                const_string_len
                assert
                push 5
                assert_eq
                
                push unicode_str
                const_string_len
                assert
                push 4
                assert_eq
            }
            
            export sentence test_char_at {
                push ascii_str
                push 1
                const_string_char_at
                assert
                push 101
                assert_eq
                
                push unicode_str
                push 3
                const_string_char_at
                assert
                push 233
                assert_eq
            }
            
            export sentence test_out_of_bounds {
                push unicode_str
                push 4
                const_string_char_at
                // Out of range, so the flag is the one place this differs from
                // the two above: it says the 0 underneath was invented.
                not
                assert
                push 0
                assert_eq
            }
        "#;
        let res = bytecode::assemble(code).unwrap();

        // Run test_len
        let test_len_idx = *res.exports.get("test_len").unwrap();
        let mut vm = VM::new(res.clone());
        assert!(vm.execute(test_len_idx).is_ok());
        assert!(vm.stack().is_empty());

        // Run test_char_at
        let test_char_idx = *res.exports.get("test_char_at").unwrap();
        let mut vm = VM::new(res.clone());
        assert!(vm.execute(test_char_idx).is_ok());
        assert!(vm.stack().is_empty());

        // Run test_out_of_bounds: an index past the end answers 0 rather than
        // failing, and reports that it did. The sentence asserts both halves.
        let oob_idx = *res.exports.get("test_out_of_bounds").unwrap();
        let mut vm = VM::new(res);
        assert!(vm.execute(oob_idx).is_ok());
        assert!(vm.stack().is_empty());
    }

    #[test]
    fn test_tracing_execution() {
        let code = r#"
            export sentence entry {
                push 42
                push 100
                add
                assert
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let entry_idx = *res.exports.get("entry").unwrap();
        let mut vm = VM::new(res);
        vm.set_tracing(true);
        assert!(vm.execute(entry_idx).is_ok());
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
                    untuple 0
                    assert
                    push 0
                }
                export function accept {
                    untuple 2
                    assert
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
                    assert
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

            export sentence test_rename {
                // Initialize state
                tuple 0
                jump renamed::init
                
                // Stack: [state] (which is 0)
                // Query accept
                pick 0
                push payload
                push to_sym
                tuple 2
                roll 1
                tuple 2
                jump renamed::accept
                assert
                
                // Query emit tuple
                pick 0
                jump renamed::emit
                untuple 2
                assert
                assert
                push payload
                push to_sym
                tuple 2
                assert_eq
                
                // Process event (payload, to_sym) -> rewrites to (payload, from_sym)
                // Stack has [0]
                push payload
                push to_sym
                tuple 2
                roll 1
                tuple 2
                jump renamed::process
                // Stack has [1] (new_state)
                pick 0
                push 1
                assert_eq
                // Query tau_reduce on state 1
                pick 0
                jump renamed::tau_reduce
                untuple 2
                assert
                pick 0
                not
                assert
                drop 0

                // Assert state value is 1
                push 1
                assert_eq
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let test_idx = *res.exports.get("test_rename").unwrap();

        let mut vm = VM::new(res);
        if let Err(e) = vm.execute(test_idx) {
            panic!("Execution failed: {}", e);
        }

        // Also test argument count error
        let bad_code = r#"
            symbol a
            symbol b
            mod m {
                export function init { untuple 0 assert push 0 }
                export sentence accept { untuple 2 assert drop 0 drop 0 push false }
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
                    assert
                }
                export function accept {
                    untuple 2
                    assert
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
                    assert
                    drop 1
                    push 100
                    add
                    assert
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

            export sentence test_closure {
                // Initialize state: should push 42, then call base::init which adds 10 -> returns 52
                tuple 0
                jump closed::init
                pick 0
                push 52
                assert_eq

                // Call process: should push 100, then add -> 152
                push 0
                roll 1
                tuple 2
                jump closed::process
                push 152
                assert_eq
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let test_idx = *res.exports.get("test_closure").unwrap();

        let mut vm = VM::new(res);
        if let Err(e) = vm.execute(test_idx) {
            panic!("Execution failed: {}", e);
        }
    }

    #[test]
    fn test_tau_reduce() {
        let code = r#"
            mod m_no_tau {
                export function init {
                    untuple 0
                    assert
                    push 0
                }
                export sentence accept {
                    untuple 2
                    assert
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
                    assert
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
                    assert
                    push 0
                }
                export sentence accept {
                    untuple 2
                    assert
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
                    assert
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

            export sentence test_tau {
                // Test m_no_tau
                tuple 0
                jump m_no_tau::init
                jump m_no_tau::tau_reduce
                untuple 2
                assert
                not
                assert
                drop 0

                // Test m_with_tau
                tuple 0
                jump m_with_tau::init
                jump m_with_tau::tau_reduce
                untuple 2
                assert
                assert
                push 1
                assert_eq
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let test_idx = *res.exports.get("test_tau").unwrap();

        let mut vm = VM::new(res);
        if let Err(e) = vm.execute(test_idx) {
            panic!("Execution failed: {}", e);
        }
    }
}

/// The executable mirror of the fallible table in `docs/totality.md`.
///
/// Every data instruction is total — it answers on every input — and a
/// **fallible** one additionally says whether the answer was computed or
/// invented, by leaving a flag on top. These tests hold the VM to the table
/// row by row, so a row changed in one place and not the other is a failure
/// rather than a silent divergence.
#[cfg(test)]
mod totality_tests {
    use super::*;
    use bytecode::arity::{is_fallible, op_arity};
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

    /// [`apply`], then split the success flag off the top.
    fn flagged(operands: &[Value], inst: Instruction) -> (Vec<Value>, bool) {
        let mut out = apply(operands, inst.clone());
        let flag = out
            .pop()
            .unwrap_or_else(|| panic!("{:?} left nothing", inst));
        match flag {
            Value::Bool(b) => (out, b),
            other => panic!("{:?} left {:?} where its flag belongs", inst, other),
        }
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
            cs("hi"),
            cs(""),
            sym(7),
            unit(),
            Value::Tuple(vec![Value::Int(1), Value::Int(2)]),
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
            Instruction::AssertEqual,
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
    /// `bin/rewrite` rewrites `roll 1 ; op` to `op` on the strength of that
    /// list, so a wrong entry would be a soundness bug in the rewriter rather
    /// than an inaccuracy in a comment. This runs every candidate on every pair
    /// of shapes both ways round and holds the list to what it finds.
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
            Instruction::IsTuple,
            Instruction::TupleLength,
            Instruction::Untuple(2),
            Instruction::Tuple(2),
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
    /// `bin/rewrite` folds `op ; is_bool` to `op ; drop ; push true` on the
    /// strength of that list. The fact cannot be derived by rewriting — a
    /// codomain is not something a case split can reach — so this is the only
    /// thing holding it to the machine.
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

    /// Every instruction that carries a flag, with operands that make it fail.
    fn failing_cases() -> Vec<(Instruction, Vec<Value>)> {
        vec![
            (Instruction::Add, vec![sym(7), Value::Int(1)]),
            (Instruction::Subtract, vec![Value::Int(1), sym(7)]),
            (
                Instruction::Multiply,
                vec![Value::Bool(true), Value::Bool(false)],
            ),
            (Instruction::Divide, vec![Value::Int(7), Value::Int(0)]),
            (Instruction::Modulo, vec![Value::Int(7), Value::Int(0)]),
            (Instruction::Negate, vec![sym(7)]),
            (Instruction::Greater, vec![sym(1), sym(2)]),
            (Instruction::Less, vec![unit(), unit()]),
            (Instruction::Untuple(3), vec![Value::Int(5)]),
            (Instruction::TupleLength, vec![sym(7)]),
            (Instruction::ConstStringLen, vec![Value::Int(3)]),
            (
                Instruction::ConstStringCharAt,
                vec![cs("hi"), Value::Int(9)],
            ),
        ]
    }

    // -- The shape of the contract ------------------------------------------

    #[test]
    fn a_fallible_instruction_keeps_its_arity_whichever_way_it_goes() {
        // The reason the flag is a stack slot rather than a second outcome: a
        // caller's stack does not depend on the data, so the arity checker
        // still works on shape alone.
        for (inst, bad) in failing_cases() {
            let (_, n_out) = op_arity(&inst).expect("a fallible instruction has a local arity");
            let failed = apply(&bad, inst.clone());
            assert_eq!(
                failed.len() as i64,
                n_out,
                "{:?} on {:?} left {} values, not {}",
                inst,
                bad,
                failed.len(),
                n_out
            );
            assert!(
                is_fallible(&inst),
                "{:?} should be listed as fallible",
                inst
            );
        }
    }

    #[test]
    fn failure_is_reported_rather_than_raised() {
        for (inst, bad) in failing_cases() {
            let (_, ok) = flagged(&bad, inst.clone());
            assert!(!ok, "{:?} on {:?} should report failure", inst, bad);
        }
    }

    #[test]
    fn success_is_reported_too() {
        let cases: Vec<(Instruction, Vec<Value>)> = vec![
            (Instruction::Add, vec![Value::Int(1), Value::Int(2)]),
            (Instruction::Divide, vec![Value::Int(7), Value::Int(2)]),
            (Instruction::Negate, vec![Value::Int(3)]),
            (Instruction::Greater, vec![Value::Int(3), Value::Int(1)]),
            (
                Instruction::Untuple(2),
                vec![Value::Tuple(vec![sym(1), sym(2)])],
            ),
            (
                Instruction::TupleLength,
                vec![Value::Tuple(vec![Value::Int(1)])],
            ),
            (Instruction::ConstStringLen, vec![cs("hi")]),
            (
                Instruction::ConstStringCharAt,
                vec![cs("hi"), Value::Int(0)],
            ),
        ];
        for (inst, good) in cases {
            let (out, ok) = flagged(&good, inst.clone());
            assert!(ok, "{:?} on {:?} should report success", inst, good);
            assert!(!out.is_empty(), "{:?} should leave a result too", inst);
        }
    }

    #[test]
    fn a_failure_hands_its_input_back_where_there_is_room_for_it() {
        // The rule that makes the flag a tag on the *stack*: an instruction
        // whose output arity has room preserves the slot its input occupied,
        // so a caller that reads the flag has not lost anything.
        assert_eq!(
            flagged(&[sym(7)], Instruction::TupleLength),
            (vec![sym(7)], false)
        );
        assert_eq!(
            flagged(&[Value::Int(3)], Instruction::ConstStringLen),
            (vec![Value::Int(3)], false)
        );
        assert_eq!(
            flagged(&[unit()], Instruction::Negate),
            (vec![unit()], false)
        );
        // `untuple n` is the one this rule is really for: the value stays in
        // the deepest of the n slots and `()` pads the rest.
        assert_eq!(
            flagged(&[sym(7)], Instruction::Untuple(3)),
            (vec![sym(7), unit(), unit()], false)
        );
        assert_eq!(
            flagged(&[sym(7)], Instruction::Untuple(1)),
            (vec![sym(7)], false)
        );
    }

    #[test]
    fn a_failure_with_no_room_fills_with_a_default() {
        // Two operands and two slots leave nowhere to keep them, which is why
        // `add` does not bother.
        assert_eq!(
            flagged(&[sym(7), Value::Int(1)], Instruction::Add),
            (vec![Value::Int(0)], false)
        );
        assert_eq!(
            flagged(&[sym(1), sym(2)], Instruction::Greater),
            (vec![Value::Bool(false)], false)
        );
        assert_eq!(
            flagged(&[cs("hi"), Value::Int(9)], Instruction::ConstStringCharAt),
            (vec![Value::Int(0)], false)
        );
        // At n = 0 there is no room either, and nothing to hold: the flag is
        // the whole answer.
        assert_eq!(
            flagged(&[Value::Int(5)], Instruction::Untuple(0)),
            (vec![], false)
        );
        assert_eq!(flagged(&[unit()], Instruction::Untuple(0)), (vec![], true));
    }

    #[test]
    fn untupling_and_retupling_recovers_the_value_it_came_from() {
        // What the preserved input buys, and the thing the previous untagged
        // junk could not do: on the failing path the value is still there, so
        // a caller that reads the flag can put the stack back exactly.
        for x in every_shape() {
            let (parts, ok) = flagged(std::slice::from_ref(&x), Instruction::Untuple(3));
            if ok {
                // A real 3-tuple rebuilds by `tuple 3`.
                let mut body: Vec<Instruction> =
                    parts.iter().cloned().map(Instruction::Push).collect();
                body.push(Instruction::Tuple(3));
                assert_eq!(run(body).unwrap(), vec![x.clone()], "rebuild of {:?}", x);
            } else {
                // Anything else left the value in the deepest slot untouched.
                assert_eq!(parts[0], x, "untuple 3 lost {:?}", x);
            }
        }
    }

    // -- The instructions that carry no flag --------------------------------

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
        // What per-operand coercion is for. `and`, `or` and `not` carry no
        // flag precisely because there is no input they cannot answer on.
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
                (Instruction::IsTuple, matches!(a, Value::Tuple(_))),
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
    fn division_by_zero_reports_rather_than_answering() {
        // `int` is the whole of arithmetic, so a zero divisor has no answer to
        // report and says so on the flag rather than inventing one.
        assert_eq!(
            flagged(&[Value::Int(1), Value::Int(0)], Instruction::Divide),
            (vec![Value::Int(0)], false)
        );
        assert_eq!(
            flagged(&[Value::Int(1), Value::Int(0)], Instruction::Modulo),
            (vec![Value::Int(0)], false)
        );
    }

    #[test]
    fn integer_arithmetic_wraps_rather_than_overflowing_the_host() {
        assert_eq!(
            flagged(&[Value::Int(i64::MIN), Value::Int(-1)], Instruction::Divide),
            (vec![Value::Int(i64::MIN)], true)
        );
        assert_eq!(
            flagged(&[Value::Int(i64::MIN), Value::Int(-1)], Instruction::Modulo),
            (vec![Value::Int(0)], true)
        );
    }

    #[test]
    fn comparisons_answer_on_two_ints_and_fail_off_the_numbers() {
        assert_eq!(
            flagged(&[Value::Int(1), Value::Int(2)], Instruction::Less),
            (vec![Value::Bool(true)], true)
        );
        // Anything that is not a pair of ints is not a comparison, and the
        // instruction reports that rather than ordering it somehow.
        let (_, ok) = flagged(&[cs("a"), Value::Int(1)], Instruction::Less);
        assert!(!ok, "a non-numeric operand is not a comparison");
    }

    // -- What is still partial ----------------------------------------------

    #[test]
    fn assert_fails_only_on_false() {
        // The sharp edge of the truthiness rule, and the reason to know which
        // way round it goes: an assertion here checks that something did not
        // definitely go wrong, not that it definitely went right. `assert` on
        // junk passes.
        for v in every_shape() {
            let got = run(vec![Instruction::Push(v.clone()), Instruction::Assert]);
            assert_eq!(
                got.is_ok(),
                v != Value::Bool(false),
                "assert on {:?} gave {:?}",
                v,
                got
            );
        }
        assert!(run(vec![Instruction::Push(Value::unit()), Instruction::Assert]).is_ok());
        assert!(
            run(vec![
                Instruction::Push(Value::Bool(false)),
                Instruction::Assert
            ])
            .is_err()
        );
    }

    #[test]
    fn assert_eq_and_panic_are_the_other_two() {
        assert!(
            run(vec![
                Instruction::Push(Value::Int(1)),
                Instruction::Push(Value::Int(2)),
                Instruction::AssertEqual,
            ])
            .is_err()
        );
        assert!(
            run(vec![
                Instruction::Push(Value::Int(1)),
                Instruction::Push(Value::Int(1)),
                Instruction::AssertEqual,
            ])
            .is_ok()
        );
        assert!(run(vec![Instruction::Panic]).is_err());
    }

    #[test]
    fn underflow_is_still_an_error_because_it_is_structural() {
        // Ruled out by arity checking rather than by a flag: a sentence that
        // would underflow does not assemble in the first place.
        for body in [
            vec![Instruction::Drop],
            vec![Instruction::Pick(0)],
            vec![Instruction::Roll(2)],
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
                    untuple 0
                    assert
                    push state::init
                }

                export sentence accept {
                    untuple 2
                    assert
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
                    assert
                    push state::init
                    equal
                    branch {
                        push event::ping
                        assert_eq
                        push state::waiting
                    } {
                        push event::pong
                        assert_eq
                        push state::done
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
                    untuple 0
                    assert
                    push 0
                }

                export sentence accept {
                    untuple 2
                    assert
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
                    assert
                    less
                    assert
                    branch {
                        push ()
                        
                        push hello
                        pick 2 // index
                        const_string_char_at
                        assert
                        
                        tuple 2 // (char, ())
                        
                        push crate::std::io::stdout::putch
                        tuple 2 // (putch, (char, ()))
                        
                        push crate::std::io::stdout::stdout
                        tuple 2 // (stdout, (putch, (char, ())))
                        
                        push crate::std::io::io
                        tuple 2 // (io, (stdout, (putch, (char, ()))))
                        
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
                    assert
                    drop 1 // drop event
                    push 1
                    add
                    assert
                }

                export function is_done {
                    push hello
                    const_string_len
                    assert
                    less
                    assert
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

/// The three laws relating `dip` to `roll`, measured against the machine.
///
/// `bin/rewrite` rewrites on the strength of these — they are what lets a law
/// stated about the top of the stack reach a value held below it — so, like
/// `Instruction::commutative` and `Instruction::yields_bool`, they are run
/// rather than asserted. Each test builds both sides of one equation and
/// checks they leave the same stack, over every depth and every shape of
/// operand the sweep can reach.
#[cfg(test)]
mod roll_law_tests {
    use super::*;
    use bytecode::value::Symbol;

    /// Distinct values, so a law that permuted them wrongly could not pass.
    fn stack_of(size: usize) -> Vec<Instruction> {
        (0..size)
            .map(|i| Instruction::Push(Value::Int(i as i64)))
            .collect()
    }

    /// Runs `body` with `helpers` reachable as sentences 1, 2, … and hands
    /// back the stack it left.
    fn run_with(body: Vec<Instruction>, helpers: Vec<Vec<Instruction>>) -> Vec<Value> {
        let mut library = Library::new();
        library.sentences.push(body);
        for h in helpers {
            library.sentences.push(h);
        }
        let mut vm = VM::new(library);
        vm.execute(SentenceIndex::from(0))
            .unwrap_or_else(|e| panic!("the law's own side failed to run: {}", e));
        vm.stack().to_vec()
    }

    fn rolls(d: usize, count: usize) -> Vec<Instruction> {
        std::iter::repeat_n(Instruction::Roll(d), count).collect()
    }

    /// The computations the sweep uses for `X`, with their arities.
    fn bodies() -> Vec<(Vec<Instruction>, usize, usize)> {
        vec![
            (vec![Instruction::IsSymbol], 1, 1),
            (vec![Instruction::Not], 1, 1),
            (vec![Instruction::Push(Value::Bool(true))], 0, 1),
            (vec![Instruction::Add], 2, 2),
            (vec![Instruction::And], 2, 1),
            (vec![Instruction::Drop], 1, 0),
            (
                vec![
                    Instruction::Push(Value::Symbol(Symbol {
                        id: 7,
                        path: "s7".to_string(),
                    })),
                    Instruction::Equal,
                ],
                1,
                1,
            ),
        ]
    }

    /// `(roll d)^(d+1)` = nothing.
    #[test]
    fn rolling_the_whole_way_round_is_the_identity() {
        for d in 0..6 {
            for extra in 0..3 {
                let size = d + 1 + extra;
                let mut lhs = stack_of(size);
                lhs.extend(rolls(d, d + 1));
                assert_eq!(
                    run_with(lhs, Vec::new()),
                    run_with(stack_of(size), Vec::new()),
                    "(roll {})^{} moved something, on a stack of {}",
                    d,
                    d + 1,
                    size
                );
            }
        }
    }

    /// `dip d { X } ; (roll (d+m-1))^m` = `(roll (d+n-1))^n ; X`.
    #[test]
    fn a_framed_computation_is_a_rolled_one() {
        for (body, n, m) in bodies() {
            for d in 0..5 {
                for extra in 0..2 {
                    let size = d + n + extra;
                    let mut lhs = stack_of(size);
                    lhs.push(Instruction::Dip(d, SentenceIndex::from(1)));
                    lhs.extend(rolls(d + m.saturating_sub(1), m));

                    let mut rhs = stack_of(size);
                    rhs.extend(rolls(d + n.saturating_sub(1), n));
                    rhs.push(Instruction::Dip(0, SentenceIndex::from(1)));

                    assert_eq!(
                        run_with(lhs, vec![body.clone()]),
                        run_with(rhs, vec![body.clone()]),
                        "dip {} {{ {:?} }} is not the rolled form, on a stack of {}",
                        d,
                        body,
                        size
                    );
                }
            }
        }
    }

    /// `pick d` = `dip d { pick 0 } ; roll d`.
    #[test]
    fn copying_from_depth_is_copying_at_depth_and_rolling_up() {
        for d in 0..6 {
            for extra in 0..3 {
                let size = d + 1 + extra;
                let mut lhs = stack_of(size);
                lhs.push(Instruction::Pick(d));

                let mut rhs = stack_of(size);
                rhs.push(Instruction::Dip(d, SentenceIndex::from(1)));
                rhs.push(Instruction::Roll(d));

                assert_eq!(
                    run_with(lhs, vec![vec![Instruction::Pick(0)]]),
                    run_with(rhs, vec![vec![Instruction::Pick(0)]]),
                    "pick {} is not the framed copy rolled up, on a stack of {}",
                    d,
                    size
                );
            }
        }
    }
}
