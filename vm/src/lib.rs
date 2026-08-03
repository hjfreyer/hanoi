use bytecode::{Instruction, Library, SentenceIndex, Value};

pub mod runtime;
pub use runtime::{Runtime, Environment, DefaultEnvironment};

/// Whether a value counts as true.
///
/// Exactly `Bool(true)` and nothing else, applied per operand. Every
/// boolean-shaped instruction — `not`, `and`, `or`, `branch`, `assert` — is
/// defined through this, which is what makes De Morgan hold on all values
/// rather than only on booleans. See `docs/totality.md`.
fn truthy(v: &Value) -> bool {
    *v == Value::Bool(true)
}

/// The junk value the untupling instructions hand back: `()`.
fn unit() -> Value {
    Value::Tuple(Vec::new())
}

/// The junk value the numeric instructions hand back.
fn zero() -> Value {
    Value::Int(0)
}

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
        self.stack.pop().ok_or_else(|| "Stack underflow".to_string())
    }

    /// Helper to peek at a value from the top of the stack.
    fn peek(&self, offset: usize) -> Result<&Value, String> {
        if self.stack.len() <= offset {
            return Err("Stack underflow on peek".to_string());
        }
        Ok(&self.stack[self.stack.len() - 1 - offset])
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
            let sentence = self.library.sentences.get(current_sentence)
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

            if let Some(limit) = self.gas_limit {
                if self.steps_executed >= limit {
                    return Err("gas limit exceeded".to_string());
                }
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
                        return Err(format!("Stack underflow on Pick: depth {} but stack size {}", depth, self.stack.len()));
                    }
                    let index = self.stack.len() - 1 - depth;
                    let val = self.stack[index].clone();
                    self.stack.push(val);
                }
                Instruction::Roll(depth) => {
                    if self.stack.len() <= depth {
                        return Err(format!("Stack underflow on Roll: depth {} but stack size {}", depth, self.stack.len()));
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
                Instruction::Greater => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let is_greater = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => x > y,
                        (Value::Float(x), Value::Float(y)) => x > y,
                        (Value::Int(x), Value::Float(y)) => (x as f64) > y,
                        (Value::Float(x), Value::Int(y)) => x > (y as f64),
                        // A non-numeric pair is not greater.
                        _ => false,
                    };
                    self.stack.push(Value::Bool(is_greater));
                }
                Instruction::Less => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let is_less = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => x < y,
                        (Value::Float(x), Value::Float(y)) => x < y,
                        (Value::Int(x), Value::Float(y)) => (x as f64) < y,
                        (Value::Float(x), Value::Int(y)) => x < (y as f64),
                        _ => false,
                    };
                    self.stack.push(Value::Bool(is_less));
                }
                Instruction::Add => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_add(y)),
                        (Value::Float(x), Value::Float(y)) => Value::Float(x + y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) + y),
                        (Value::Float(x), Value::Int(y)) => Value::Float(x + (y as f64)),
                        _ => zero(),
                    };
                    self.stack.push(res);
                }
                Instruction::Subtract => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_sub(y)),
                        (Value::Float(x), Value::Float(y)) => Value::Float(x - y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) - y),
                        (Value::Float(x), Value::Int(y)) => Value::Float(x - (y as f64)),
                        _ => zero(),
                    };
                    self.stack.push(res);
                }
                Instruction::Multiply => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_mul(y)),
                        (Value::Float(x), Value::Float(y)) => Value::Float(x * y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) * y),
                        (Value::Float(x), Value::Int(y)) => Value::Float(x * (y as f64)),
                        _ => zero(),
                    };
                    self.stack.push(res);
                }
                Instruction::Divide => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        // Integer division by zero is zero, following Lean.
                        // `wrapping_div` additionally keeps `i64::MIN / -1`
                        // from being a host-level overflow.
                        (Value::Int(_), Value::Int(0)) => zero(),
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_div(y)),
                        // The float world is uniformly IEEE: an `Int` divisor
                        // coerces like any other mixed operand rather than
                        // being an excuse to leave it.
                        (Value::Float(x), Value::Float(y)) => Value::Float(x / y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) / y),
                        (Value::Float(x), Value::Int(y)) => Value::Float(x / (y as f64)),
                        _ => zero(),
                    };
                    self.stack.push(res);
                }
                Instruction::Modulo => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        (Value::Int(_), Value::Int(0)) => zero(),
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_rem(y)),
                        (Value::Float(x), Value::Float(y)) => Value::Float(x % y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) % y),
                        (Value::Float(x), Value::Int(y)) => Value::Float(x % (y as f64)),
                        _ => zero(),
                    };
                    self.stack.push(res);
                }
                Instruction::Not => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(!truthy(&val)));
                }
                Instruction::And => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(Value::Bool(truthy(&a) && truthy(&b)));
                }
                Instruction::Or => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.stack.push(Value::Bool(truthy(&a) || truthy(&b)));
                }
                Instruction::Negate => {
                    let val = self.pop()?;
                    let res = match val {
                        Value::Int(x) => Value::Int(x.wrapping_neg()),
                        Value::Float(x) => Value::Float(-x),
                        _ => zero(),
                    };
                    self.stack.push(res);
                }
                Instruction::Print => {
                    let val = self.peek(0)?;
                    println!("{}", val);
                }
                Instruction::Dip(depth, target) => {
                    if self.stack.len() < depth {
                        return Err(format!("Stack underflow on Dip: depth {} but stack size {}", depth, self.stack.len()));
                    }
                    // Withhold the top `depth` values for the duration of the call.
                    let hidden = self.stack.split_off(self.stack.len() - depth);
                    self.call_stack.push(Frame { sentence: current_sentence, ip, hidden });
                    current_sentence = target;
                    ip = 0;
                }
                Instruction::Branch(then_target, else_target) => {
                    let cond = self.pop()?;
                    // The then arm is reached by `Bool(true)` and nothing else;
                    // every other value takes the else arm, agreeing with junk
                    // being falsy everywhere.
                    let b = truthy(&cond);
                    // Push the return address (the next instruction) to the call stack
                    self.call_stack.push(Frame { sentence: current_sentence, ip, hidden: Vec::new() });
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
                    if !truthy(&val) {
                        return Err(format!("Assertion failed: {:?} is not true", val));
                    }
                }
                Instruction::AssertEqual => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    if a != b {
                        return Err(format!("Assertion failed: values are not equal: {:?} != {:?}", a, b));
                    }
                }
                Instruction::Tuple(n) => {
                    if self.stack.len() < n {
                        return Err(format!("Stack underflow on Tuple: requested {} but stack size {}", n, self.stack.len()));
                    }
                    let index = self.stack.len() - n;
                    let mut elements = self.stack.split_off(index);
                    elements.reverse();
                    self.stack.push(Value::Tuple(elements));
                }
                Instruction::Untuple(n) => {
                    // Anything that is not an n-tuple comes apart into n
                    // copies of `()`. The junk is untagged on purpose: `Tuple`
                    // stays a free constructor, at the cost of `untuple n;
                    // tuple n` being a junk-normalization rather than the
                    // identity. See `docs/totality.md`.
                    let val = self.pop()?;
                    match val {
                        Value::Tuple(elements) if elements.len() == n => {
                            for elem in elements.into_iter().rev() {
                                self.stack.push(elem);
                            }
                        }
                        _ => self.stack.extend(std::iter::repeat(unit()).take(n)),
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
                Instruction::IsFloat => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(val, Value::Float(_))));
                }
                Instruction::IsSymbol => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(val, Value::Symbol(_))));
                }
                Instruction::IsTuple => {
                    let val = self.pop()?;
                    self.stack.push(Value::Bool(matches!(val, Value::Tuple(_))));
                }
                Instruction::TupleLength => {
                    // Zero for a non-tuple. That is what lets a guard read
                    // `tuple_length; push n; equal` as "is an n-tuple" without
                    // an `is_tuple` in front of it, for every n >= 1.
                    let val = self.pop()?;
                    let len = match val {
                        Value::Tuple(elements) => elements.len() as i64,
                        _ => 0,
                    };
                    self.stack.push(Value::Int(len));
                }
                Instruction::SymbolLen => {
                    let val = self.pop()?;
                    let len = match val {
                        Value::Symbol(sym) => sym.name.chars().count() as i64,
                        _ => 0,
                    };
                    self.stack.push(Value::Int(len));
                }
                Instruction::SymbolCharAt => {
                    let idx_val = self.pop()?;
                    let sym_val = self.pop()?;
                    // Wrong types and an out-of-range index answer alike: an
                    // index is in range or it is not, and there is nothing for
                    // a caller to learn from telling the two apart.
                    let ch = match (sym_val, idx_val) {
                        (Value::Symbol(sym), Value::Int(idx)) => usize::try_from(idx)
                            .ok()
                            .and_then(|idx| sym.name.chars().nth(idx))
                            .map(|ch| ch as i64)
                            .unwrap_or(0),
                        _ => 0,
                    };
                    self.stack.push(Value::Int(ch));
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
            Instruction::Pick(0), // Dup
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
        let s1 = vec![
            Instruction::Push(Value::Int(42)),
        ];
        let s2 = vec![
            Instruction::Push(Value::Bool(false)),
            Instruction::Assert,
        ];

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
        let s1 = vec![
            Instruction::Push(Value::Int(10)),
        ];

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
            Instruction::Dip(0, SentenceIndex::from(1)),
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
            Instruction::Dip(1, SentenceIndex::from(1)),
        ];
        let s1 = vec![Instruction::Dip(1, SentenceIndex::from(2))];
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

            // test is_float
            Instruction::Push(Value::Float(3.14)),
            Instruction::IsFloat,
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
        let sentence = vec![
            Instruction::Push(Value::Bool(false)),
            Instruction::Assert,
        ];
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
            symbol status_ok "Successful execution"
            symbol status_error "Execution error"
            
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
    fn test_symbol_len_and_char_at() {
        let code = r#"
            symbol ascii_sym "hello"
            symbol unicode_sym "café"
            
            export sentence test_len {
                push ascii_sym
                symbol_len
                push 5
                assert_eq
                
                push unicode_sym
                symbol_len
                push 4
                assert_eq
            }
            
            export sentence test_char_at {
                push ascii_sym
                push 1
                symbol_char_at
                push 101
                assert_eq
                
                push unicode_sym
                push 3
                symbol_char_at
                push 233
                assert_eq
            }
            
            export sentence test_out_of_bounds {
                push unicode_sym
                push 4
                symbol_char_at
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
        // failing, and the sentence asserts exactly that.
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
                symbol start "Start test event"
                symbol pass "Pass test event"
                symbol fail "Fail test event"
            }

            symbol from_sym "FromSymbol"
            symbol to_sym "ToSymbol"
            symbol payload "Payload"
            mod base {
                export function init {
                    untuple 0
                    push 0
                }
                export function accept {
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
            mod m { export function init { untuple 0 push 0 } export sentence accept { untuple 2 drop 0 drop 0 push false } export function emit { drop 0 tuple 0 push false tuple 2 } export sentence process { } }
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

            export sentence test_tau {
                // Test m_no_tau
                tuple 0
                jump m_no_tau::init
                jump m_no_tau::tau_reduce
                untuple 2
                not
                assert
                drop 0

                // Test m_with_tau
                tuple 0
                jump m_with_tau::init
                jump m_with_tau::tau_reduce
                untuple 2
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

/// The executable mirror of the junk table in `docs/totality.md`.
///
/// One test per group of rows, and between them every data instruction is
/// applied to at least one operand it was not written for. The table is the
/// spec and this is what holds the VM to it, so a row changed in one place and
/// not the other is a test failure rather than a silent divergence.
#[cfg(test)]
mod totality_tests {
    use super::*;
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
    /// Panics if the instruction failed, which is the point: a data
    /// instruction is total, so `apply` having a `Result` at all would be
    /// admitting the thing under test.
    fn apply(operands: &[Value], inst: Instruction) -> Vec<Value> {
        let mut body: Vec<Instruction> = operands.iter().cloned().map(Instruction::Push).collect();
        body.push(inst.clone());
        run(body).unwrap_or_else(|e| panic!("{:?} on {:?} failed: {}", inst, operands, e))
    }

    fn sym(name: &str) -> Value {
        Value::Symbol(Symbol {
            id: 7,
            name: name.to_string(),
        })
    }

    fn unit() -> Value {
        Value::Tuple(Vec::new())
    }

    /// One value of each shape, plus a couple of edge cases. Anything claimed
    /// to hold "on every value" is checked against all of these.
    fn every_shape() -> Vec<Value> {
        vec![
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(-3),
            Value::Float(1.5),
            sym("s"),
            unit(),
            Value::Tuple(vec![Value::Int(1), Value::Int(2)]),
        ]
    }

    // -- Truthiness ---------------------------------------------------------

    #[test]
    fn only_bool_true_is_true() {
        for v in every_shape() {
            let expected = v == Value::Bool(true);
            assert_eq!(
                apply(&[v.clone()], Instruction::Not),
                vec![Value::Bool(!expected)],
                "not {:?}",
                v
            );
        }
        // The deliberate oddity: junk is not true, so its negation is.
        assert_eq!(
            apply(&[Value::Int(42)], Instruction::Not),
            vec![Value::Bool(true)]
        );
    }

    #[test]
    fn and_and_or_coerce_each_operand_separately() {
        for a in every_shape() {
            for b in every_shape() {
                let (p, q) = (a == Value::Bool(true), b == Value::Bool(true));
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
        // What per-operand coercion is for. Coercing the pair jointly, or
        // having `and` return one of its operands, would both break this.
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
    fn a_branch_takes_the_else_arm_on_anything_but_true() {
        for v in every_shape() {
            let mut library = Library::new();
            library.sentences.push(vec![
                Instruction::Push(v.clone()),
                Instruction::Branch(SentenceIndex::from(1), SentenceIndex::from(2)),
            ]);
            library.sentences.push(vec![Instruction::Push(Value::Int(1))]);
            library.sentences.push(vec![Instruction::Push(Value::Int(2))]);

            let mut vm = VM::new(library);
            vm.execute(SentenceIndex::from(0))
                .unwrap_or_else(|e| panic!("branch on {:?} failed: {}", v, e));
            let taken = if v == Value::Bool(true) { 1 } else { 2 };
            assert_eq!(vm.stack(), &[Value::Int(taken)], "branch on {:?}", v);
        }
    }

    // -- Numbers ------------------------------------------------------------

    #[test]
    fn arithmetic_on_a_non_numeric_pair_is_zero() {
        for inst in [
            Instruction::Add,
            Instruction::Subtract,
            Instruction::Multiply,
            Instruction::Divide,
            Instruction::Modulo,
        ] {
            for operands in [
                [sym("s"), Value::Int(1)],
                [Value::Int(1), sym("s")],
                [Value::Bool(true), Value::Bool(false)],
                [unit(), Value::Float(1.0)],
            ] {
                assert_eq!(
                    apply(&operands, inst.clone()),
                    vec![Value::Int(0)],
                    "{:?} on {:?}",
                    inst,
                    operands
                );
            }
        }
        assert_eq!(
            apply(&[sym("s")], Instruction::Negate),
            vec![Value::Int(0)]
        );
    }

    #[test]
    fn integer_division_by_zero_is_zero() {
        assert_eq!(
            apply(&[Value::Int(7), Value::Int(0)], Instruction::Divide),
            vec![Value::Int(0)]
        );
        assert_eq!(
            apply(&[Value::Int(7), Value::Int(0)], Instruction::Modulo),
            vec![Value::Int(0)]
        );
        // And the other host-level overflow that used to be reachable.
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
    fn the_float_world_stays_ieee_even_with_an_int_divisor() {
        // An `Int` zero coerces like any other mixed operand rather than
        // dragging the expression back into the integer convention.
        let [Value::Float(q)] = apply(&[Value::Float(1.0), Value::Int(0)], Instruction::Divide)[..]
        else {
            panic!("expected a float")
        };
        assert!(q.is_infinite() && q > 0.0, "1.0 / 0 should be inf, got {}", q);

        let [Value::Float(r)] = apply(&[Value::Float(1.0), Value::Int(0)], Instruction::Modulo)[..]
        else {
            panic!("expected a float")
        };
        assert!(r.is_nan(), "1.0 % 0 should be NaN, got {}", r);
    }

    #[test]
    fn comparisons_of_a_non_numeric_pair_are_false() {
        for inst in [Instruction::Greater, Instruction::Less] {
            for operands in [
                [sym("a"), sym("b")],
                [Value::Int(1), Value::Bool(true)],
                [unit(), unit()],
            ] {
                assert_eq!(
                    apply(&operands, inst.clone()),
                    vec![Value::Bool(false)],
                    "{:?} on {:?}",
                    inst,
                    operands
                );
            }
        }
        // Numbers still compare, mixed pairs included.
        assert_eq!(
            apply(&[Value::Int(1), Value::Float(1.5)], Instruction::Less),
            vec![Value::Bool(true)]
        );
    }

    // -- Tuples and symbols -------------------------------------------------

    #[test]
    fn untupling_a_non_tuple_yields_units() {
        for v in [sym("s"), Value::Int(3), Value::Tuple(vec![Value::Int(1)])] {
            assert_eq!(
                apply(&[v.clone()], Instruction::Untuple(3)),
                vec![unit(), unit(), unit()],
                "untuple 3 on {:?}",
                v
            );
        }
        // Including the degenerate widths.
        assert_eq!(apply(&[Value::Int(3)], Instruction::Untuple(0)), vec![]);
        assert_eq!(
            apply(&[Value::Int(3)], Instruction::Untuple(1)),
            vec![unit()]
        );
    }

    #[test]
    fn untupling_then_retupling_normalizes_rather_than_panicking() {
        // Why `cancel_tuple` is still one-way: this is a real function, and
        // not the identity.
        assert_eq!(
            run(vec![
                Instruction::Push(sym("s")),
                Instruction::Untuple(2),
                Instruction::Tuple(2),
            ])
            .unwrap(),
            vec![Value::Tuple(vec![unit(), unit()])]
        );
        // But it is idempotent through a second untuple, which is what makes
        // the normalization invisible to anything that takes it apart again.
        assert_eq!(
            run(vec![
                Instruction::Push(sym("s")),
                Instruction::Untuple(2),
                Instruction::Tuple(2),
                Instruction::Untuple(2),
            ])
            .unwrap(),
            apply(&[sym("s")], Instruction::Untuple(2))
        );
    }

    #[test]
    fn tuple_length_of_a_non_tuple_is_zero() {
        for v in [sym("s"), Value::Int(3), Value::Bool(true)] {
            assert_eq!(
                apply(&[v.clone()], Instruction::TupleLength),
                vec![Value::Int(0)],
                "tuple_length of {:?}",
                v
            );
        }
        // The guard `rebuild_copy` relies on: zero is not a width any real
        // n-tuple reports for n >= 1.
        assert_eq!(apply(&[unit()], Instruction::TupleLength), vec![Value::Int(0)]);
    }

    #[test]
    fn symbol_length_of_a_non_symbol_is_zero() {
        for v in [Value::Int(3), unit(), Value::Bool(false)] {
            assert_eq!(
                apply(&[v.clone()], Instruction::SymbolLen),
                vec![Value::Int(0)],
                "symbol_len of {:?}",
                v
            );
        }
    }

    #[test]
    fn symbol_char_at_answers_zero_off_the_end_and_off_the_type() {
        let s = sym("hi");
        for idx in [-1i64, 2, 9999] {
            assert_eq!(
                apply(&[s.clone(), Value::Int(idx)], Instruction::SymbolCharAt),
                vec![Value::Int(0)],
                "index {}",
                idx
            );
        }
        assert_eq!(
            apply(&[Value::Int(1), Value::Int(0)], Instruction::SymbolCharAt),
            vec![Value::Int(0)]
        );
        assert_eq!(
            apply(&[s.clone(), sym("nope")], Instruction::SymbolCharAt),
            vec![Value::Int(0)]
        );
        // In range still answers.
        assert_eq!(
            apply(&[s, Value::Int(0)], Instruction::SymbolCharAt),
            vec![Value::Int('h' as i64)]
        );
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
                (Instruction::IsFloat, matches!(a, Value::Float(_))),
                (Instruction::IsSymbol, matches!(a, Value::Symbol(_))),
                (Instruction::IsTuple, matches!(a, Value::Tuple(_))),
            ] {
                assert_eq!(
                    apply(&[a.clone()], inst.clone()),
                    vec![Value::Bool(want)],
                    "{:?} of {:?}",
                    inst,
                    a
                );
            }
        }
    }

    // -- What is still partial ----------------------------------------------

    #[test]
    fn assert_fails_on_anything_that_is_not_true() {
        for v in every_shape() {
            let got = run(vec![Instruction::Push(v.clone()), Instruction::Assert]);
            assert_eq!(
                got.is_ok(),
                v == Value::Bool(true),
                "assert on {:?} gave {:?}",
                v,
                got
            );
        }
    }

    #[test]
    fn assert_eq_and_panic_are_the_other_two() {
        assert!(run(vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(2)),
            Instruction::AssertEqual,
        ])
        .is_err());
        assert!(run(vec![
            Instruction::Push(Value::Int(1)),
            Instruction::Push(Value::Int(1)),
            Instruction::AssertEqual,
        ])
        .is_ok());
        assert!(run(vec![Instruction::Panic]).is_err());
    }

    #[test]
    fn underflow_is_still_an_error_because_it_is_structural() {
        // Ruled out by arity checking rather than by a junk value: a sentence
        // that would underflow does not assemble in the first place.
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
                    if sym.name == "ping event" {
                        self.received_ping = true;
                        return Ok(());
                    }
                    Err(format!("Unexpected symbol event: {}", sym.name))
                }
                other => Err(format!("Unexpected event type: {:?}", other))
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
                    symbol init "initial state"
                    symbol waiting "waiting state"
                    symbol done "done state"
                }

                mod event {
                    symbol ping "ping event"
                    symbol pong "pong event"
                }

                export function init {
                    untuple 0
                    push state::init
                }

                export sentence accept {
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
        let pong_symbol = res.symbols.get("main::event::pong").cloned()
            .and_then(|v| match v {
                Value::Symbol(s) => Some(s),
                _ => None,
            })
            .unwrap();
        let env = TestEnv { pong_symbol, received_ping: false };
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
                    symbol io "std::io"
                    mod stdout {
                        symbol stdout "std::io::stdout"
                        symbol putch "std::io::stdout::putch"
                    }
                }
            }

            mod main {
                symbol hello "Hello, World!"

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

                export function tau_reduce {
                    push false
                    tuple 2
                }

                export function emit {
                    pick 0
                    push hello
                    symbol_len
                    less
                    branch {
                        push ()
                        
                        push hello
                        pick 2 // index
                        symbol_char_at
                        
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
                    drop 1 // drop event
                    push 1
                    add
                }

                export function is_done {
                    push hello
                    symbol_len
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
