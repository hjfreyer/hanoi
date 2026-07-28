use bytecode::{Instruction, Library, SentenceIndex, Value};

pub mod runtime;
pub use runtime::{Runtime, Environment, DefaultEnvironment};

/// The virtual machine that executes sentences from a loaded library.
pub struct VM {
    library: Library,
    stack: Vec<Value>,
    call_stack: Vec<(SentenceIndex, usize)>,
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
                if let Some((caller_sentence, caller_ip)) = self.call_stack.pop() {
                    if self.tracing {
                        println!(
                            "[TRACE] Returning to Sentence: {:?}, IP: {}",
                            caller_sentence, caller_ip
                        );
                    }
                    current_sentence = caller_sentence;
                    ip = caller_ip;
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
                    "[TRACE] Sentence: {:?}, IP: {}, Instruction: {:?} | Stack: {:?}",
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
                Instruction::Drop(depth) => {
                    if self.stack.len() <= depth {
                        return Err(format!("Stack underflow on Drop: depth {} but stack size {}", depth, self.stack.len()));
                    }
                    let index = self.stack.len() - 1 - depth;
                    self.stack.remove(index);
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
                        (v1, v2) => return Err(format!("Cannot compare Greater between non-numeric values {} and {}", v1, v2)),
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
                        (v1, v2) => return Err(format!("Cannot compare Less between non-numeric values {} and {}", v1, v2)),
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
                        (v1, v2) => return Err(format!("Cannot add non-numeric values {} and {}", v1, v2)),
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
                        (v1, v2) => return Err(format!("Cannot subtract non-numeric values {} and {}", v1, v2)),
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
                        (v1, v2) => return Err(format!("Cannot multiply non-numeric values {} and {}", v1, v2)),
                    };
                    self.stack.push(res);
                }
                Instruction::Divide => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => {
                            if y == 0 {
                                return Err("Division by zero".to_string());
                            }
                            Value::Int(x / y)
                        }
                        (Value::Float(x), Value::Float(y)) => Value::Float(x / y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) / y),
                        (Value::Float(x), Value::Int(y)) => {
                            if y == 0 {
                                return Err("Division by zero".to_string());
                            }
                            Value::Float(x / (y as f64))
                        }
                        (v1, v2) => return Err(format!("Cannot divide non-numeric values {} by {}", v1, v2)),
                    };
                    self.stack.push(res);
                }
                Instruction::Modulo => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let res = match (a, b) {
                        (Value::Int(x), Value::Int(y)) => {
                            if y == 0 {
                                return Err("Modulo by zero".to_string());
                            }
                            Value::Int(x % y)
                        }
                        (Value::Float(x), Value::Float(y)) => Value::Float(x % y),
                        (Value::Int(x), Value::Float(y)) => Value::Float((x as f64) % y),
                        (Value::Float(x), Value::Int(y)) => {
                            if y == 0 {
                                return Err("Modulo by zero".to_string());
                            }
                            Value::Float(x % (y as f64))
                        }
                        (v1, v2) => return Err(format!("Cannot modulo non-numeric values {} by {}", v1, v2)),
                    };
                    self.stack.push(res);
                }
                Instruction::Not => {
                    let val = self.pop()?;
                    let b = match val {
                        Value::Bool(b) => b,
                        v => return Err(format!("Expected boolean operand on Not, found {:?}", v)),
                    };
                    self.stack.push(Value::Bool(!b));
                }
                Instruction::And => {
                    let b_val = self.pop()?;
                    let a_val = self.pop()?;
                    let (a, b) = match (a_val, b_val) {
                        (Value::Bool(a), Value::Bool(b)) => (a, b),
                        (v1, v2) => return Err(format!("Expected boolean operands on And, found {:?} and {:?}", v1, v2)),
                    };
                    self.stack.push(Value::Bool(a && b));
                }
                Instruction::Or => {
                    let b_val = self.pop()?;
                    let a_val = self.pop()?;
                    let (a, b) = match (a_val, b_val) {
                        (Value::Bool(a), Value::Bool(b)) => (a, b),
                        (v1, v2) => return Err(format!("Expected boolean operands on Or, found {:?} and {:?}", v1, v2)),
                    };
                    self.stack.push(Value::Bool(a || b));
                }
                Instruction::Negate => {
                    let val = self.pop()?;
                    let res = match val {
                        Value::Int(x) => Value::Int(x.wrapping_neg()),
                        Value::Float(x) => Value::Float(-x),
                        v => return Err(format!("Cannot negate non-numeric value: {}", v)),
                    };
                    self.stack.push(res);
                }
                Instruction::Print => {
                    let val = self.peek(0)?;
                    println!("{}", val);
                }
                Instruction::Jump(target) => {
                    // Push the return address (the next instruction) to the call stack
                    self.call_stack.push((current_sentence, ip));
                    current_sentence = target;
                    ip = 0;
                }
                Instruction::Branch(then_target, else_target) => {
                    let cond = self.pop()?;
                    let b = match cond {
                        Value::Bool(b) => b,
                        v => return Err(format!("Expected boolean condition on Branch, found {:?}", v)),
                    };
                    // Push the return address (the next instruction) to the call stack
                    self.call_stack.push((current_sentence, ip));
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
                    let val = self.pop()?;
                    let b = match val {
                        Value::Bool(b) => b,
                        v => return Err(format!("Expected boolean operand on Assert, found {:?}", v)),
                    };
                    if !b {
                        return Err(format!("Assertion failed: value is false"));
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
                    let val = self.pop()?;
                    if let Value::Tuple(elements) = val {
                        if elements.len() != n {
                            return Err(format!("Tuple size mismatch on Untuple: expected {} but tuple has {}", n, elements.len()));
                        }
                        for elem in elements.into_iter().rev() {
                            self.stack.push(elem);
                        }
                    } else {
                        return Err(format!("Expected Value::Tuple on Untuple, found {:?}", val));
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
                    let val = self.pop()?;
                    if let Value::Tuple(elements) = val {
                        self.stack.push(Value::Int(elements.len() as i64));
                    } else {
                        return Err(format!("Expected Value::Tuple on tuple_length, found {:?}", val));
                    }
                }
                Instruction::SymbolLen => {
                    let val = self.pop()?;
                    if let Value::Symbol(sym) = val {
                        self.stack.push(Value::Int(sym.name.chars().count() as i64));
                    } else {
                        return Err(format!("Expected Value::Symbol on symbol_len, found {:?}", val));
                    }
                }
                Instruction::SymbolCharAt => {
                    let idx_val = self.pop()?;
                    let sym_val = self.pop()?;
                    match (sym_val, idx_val) {
                        (Value::Symbol(sym), Value::Int(idx)) => {
                            let char_count = sym.name.chars().count() as i64;
                            if idx < 0 || idx >= char_count {
                                return Err(format!("Symbol index out of bounds: index {} on symbol '{}' of length {}", idx, sym.name, char_count));
                            }
                            let ch = sym.name.chars().nth(idx as usize).unwrap();
                            self.stack.push(Value::Int(ch as i64));
                        }
                        (s, i) => {
                            return Err(format!("Invalid arguments to symbol_char_at: expected Symbol, Int, found {:?}, {:?}", s, i));
                        }
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

        // sentence 0: Push 10, Jump to sentence 1, then AssertEqual (verifying that sentence 1 ran and returned to s0)
        let s0 = vec![
            Instruction::Push(Value::Int(10)),
            Instruction::Jump(SentenceIndex::from(1)),
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
        
        // Run test_out_of_bounds (should fail)
        let oob_idx = *res.exports.get("test_out_of_bounds").unwrap();
        let mut vm = VM::new(res);
        let run_res = vm.execute(oob_idx);
        assert!(run_res.is_err());
        assert!(run_res.unwrap_err().contains("Symbol index out of bounds"));
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
