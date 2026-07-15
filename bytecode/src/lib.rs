pub mod assembly;
pub mod library;
pub mod opcode;
pub mod value;

pub use assembly::{assemble, AssemblyResult};
pub use library::{Library, Sentence, SentenceIndex};
pub use opcode::Instruction;
pub use value::Value;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_display() {
        assert_eq!(format!("{}", Value::Nil), "nil");
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::Float(3.14)), "3.14");
    }

    #[test]
    fn test_instruction_equality() {
        let inst1 = Instruction::Push(Value::Int(42));
        let inst2 = Instruction::Push(Value::Int(42));
        let inst3 = Instruction::Drop(0);

        assert_eq!(inst1, inst2);
        assert_ne!(inst1, inst3);
    }

    #[test]
    fn test_library_indexing() {
        let mut library = Library::new();
        let sentence1 = vec![
            Instruction::Push(Value::Int(10)),
            Instruction::Drop(0),
        ];
        let sentence2 = vec![
            Instruction::Push(Value::Int(20)),
            Instruction::Drop(0),
        ];

        library.sentences.push(sentence1.clone());
        library.sentences.push(sentence2.clone());

        let idx1 = SentenceIndex::from(0);
        let idx2 = SentenceIndex::from(1);

        assert_eq!(library.sentences[idx1], sentence1);
        assert_eq!(library.sentences[idx2], sentence2);
    }

    #[test]
    fn test_assemble_simple() {
        let code = r#"
            export entry {
                push 42
                push (1, 2, (3, nil))
                drop 1
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.exports.get("entry"), Some(&SentenceIndex::from(0)));
        assert_eq!(res.library.sentences.len(), 1);
        assert_eq!(
            res.library.sentences[SentenceIndex::from(0)],
            vec![
                Instruction::Push(Value::Int(42)),
                Instruction::Push(Value::Tuple(vec![
                    Value::Int(1),
                    Value::Int(2),
                    Value::Tuple(vec![Value::Int(3), Value::Nil])
                ])),
                Instruction::Drop(1),
            ]
        );
    }

    #[test]
    fn test_assemble_nested_branching() {
        let code = r#"
            entry {
                push true
                branch {
                    push 42
                } {
                    jump entry
                }
            }
        "#;
        let res = assemble(code).unwrap();
        // Should have compiled 3 sentences:
        // Index 0: entry
        // Index 1: inline true block
        // Index 2: inline false block
        assert_eq!(res.library.sentences.len(), 3);
        assert_eq!(
            res.library.sentences[SentenceIndex::from(0)],
            vec![
                Instruction::Push(Value::Bool(true)),
                Instruction::Branch(SentenceIndex::from(1), SentenceIndex::from(2)),
            ]
        );
        assert_eq!(
            res.library.sentences[SentenceIndex::from(1)],
            vec![Instruction::Push(Value::Int(42))]
        );
        assert_eq!(
            res.library.sentences[SentenceIndex::from(2)],
            vec![Instruction::Jump(SentenceIndex::from(0))]
        );
    }

    #[test]
    fn test_assemble_invalid_label() {
        let code = r#"
            entry {
                jump non_existent_label
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Unresolved label target"));
    }

    #[test]
    fn test_assemble_symbols() {
        let code = r#"
            symbol sym1 "My Custom Symbol"
            symbol sym2
            
            entry {
                push sym1
                push sym2
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.library.sentences.len(), 1);
        
        let sentence = &res.library.sentences[SentenceIndex::from(0)];
        assert_eq!(sentence.len(), 2);
        
        // Assert sym1 and sym2 are distinct symbols
        if let (Instruction::Push(Value::Symbol(s1)), Instruction::Push(Value::Symbol(s2))) = (&sentence[0], &sentence[1]) {
            assert_ne!(s1, s2);
            assert_eq!(s1.name, "My Custom Symbol");
            assert_eq!(s2.name, "sym2");
        } else {
            panic!("Expected pushing of two symbols");
        }
    }

    #[test]
    fn test_assemble_test_annotation() {
        let code = r#"
            test my_test {
                push 1
                assert
            }
            export test my_exported_test {
                push 2
                assert
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.tests.get("my_test"), Some(&SentenceIndex::from(0)));
        assert_eq!(res.tests.get("my_exported_test"), Some(&SentenceIndex::from(1)));
        assert_eq!(res.exports.get("my_exported_test"), Some(&SentenceIndex::from(1)));
        assert_eq!(res.exports.get("my_test"), None);
    }
}
