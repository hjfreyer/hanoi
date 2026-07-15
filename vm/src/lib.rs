use bytecode::{Instruction, Library, SentenceIndex, Value};

/// The virtual machine that executes sentences from a loaded library.
pub struct VM {
    library: Library,
    stack: Vec<Value>,
    call_stack: Vec<(SentenceIndex, usize)>,
}

impl VM {
    /// Creates a new VM initialized with the given library.
    pub fn new(library: Library) -> Self {
        Self {
            library,
            stack: Vec::new(),
            call_stack: Vec::new(),
        }
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

    /// Helper to determine the truthiness of a value.
    /// Nil is falsey. Bool(false) is falsey. Numbers equal to zero are falsey.
    /// Tuples are always truthy. Everything else is truthy.
    fn is_truthy(&self, value: &Value) -> bool {
        match value {
            Value::Nil => false,
            Value::Bool(b) => *b,
            Value::Int(x) => *x != 0,
            Value::Float(x) => *x != 0.0 && !x.is_nan(),
            Value::Tuple(_) => true,
        }
    }

    /// Executes sentences in the library starting with the given `start_sentence`.
    /// Reaching the end of a sentence pops the call stack to return to the caller.
    /// Execution terminates when the call stack is empty and the current sentence ends.
    pub fn execute(&mut self, start_sentence: SentenceIndex) -> Result<(), String> {
        let mut current_sentence = start_sentence;
        let mut ip = 0;

        loop {
            // Get the sentence reference
            let sentence = self.library.sentences.get(current_sentence)
                .ok_or_else(|| format!("Invalid sentence index: {:?}", current_sentence))?;

            if ip >= sentence.len() {
                // Return to the caller if there's an address on the call stack
                if let Some((caller_sentence, caller_ip)) = self.call_stack.pop() {
                    current_sentence = caller_sentence;
                    ip = caller_ip;
                    continue;
                } else {
                    // Terminate execution if the call stack is empty
                    break;
                }
            }

            // Clone the instruction to release the borrow on self.library
            let instruction = sentence[ip].clone();
            ip += 1;

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
                    self.stack.push(Value::Bool(!self.is_truthy(&val)));
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
                    // Push the return address (the next instruction) to the call stack
                    self.call_stack.push((current_sentence, ip));
                    if self.is_truthy(&cond) {
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
                    if !self.is_truthy(&val) {
                        return Err(format!("Assertion failed: value {:?} is falsey", val));
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
                    let elements = self.stack.split_off(index);
                    self.stack.push(Value::Tuple(elements));
                }
                Instruction::Untuple(n) => {
                    let val = self.pop()?;
                    if let Value::Tuple(elements) = val {
                        if elements.len() != n {
                            return Err(format!("Tuple size mismatch on Untuple: expected {} but tuple has {}", n, elements.len()));
                        }
                        for elem in elements {
                            self.stack.push(elem);
                        }
                    } else {
                        return Err(format!("Expected Value::Tuple on Untuple, found {:?}", val));
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
        // push 1, push 2, push 3, tuple(3) -> Tuple(1, 2, 3)
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
            export start {
                push 10
                push 20
                add
                push 30
                assert_eq
                
                # Test branching with inline targets
                push true
                branch {
                    push 100
                } {
                    panic
                }
                
                # Check that the branch returned and we continue here
                push 100
                assert_eq
            }
        "#;
        let res = bytecode::assemble(code).unwrap();
        let start_idx = *res.exports.get("start").unwrap();
        
        let mut vm = VM::new(res.library);
        assert!(vm.execute(start_idx).is_ok());
        assert!(vm.stack().is_empty());
    }
}
