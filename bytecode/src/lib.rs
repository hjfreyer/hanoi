pub mod arity;
pub mod assembly;
pub mod library;
pub mod opcode;
pub mod value;
pub mod safety;

pub use arity::check_arities;
pub use assembly::{assemble, assemble_with_path};
pub use library::{Library, Sentence, SentenceIndex, Annotation, Arity};
pub use opcode::Instruction;
pub use value::Value;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_display() {
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
            export sentence entry {
                push 42
                push (1, 2, (3, false))
                drop 1
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.exports.get("entry"), Some(&SentenceIndex::from(0)));
        assert_eq!(res.sentences.len(), 1);
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![
                Instruction::Push(Value::Int(42)),
                Instruction::Push(Value::Tuple(vec![
                    Value::Int(1),
                    Value::Int(2),
                    Value::Tuple(vec![Value::Int(3), Value::Bool(false)])
                ])),
                Instruction::Drop(1),
            ]
        );
    }

    #[test]
    fn test_assemble_nested_branching() {
        let code = r#"
            #[recursive]
            sentence entry {
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
        assert_eq!(res.sentences.len(), 3);
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![
                Instruction::Push(Value::Bool(true)),
                Instruction::Branch(SentenceIndex::from(1), SentenceIndex::from(2)),
            ]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Push(Value::Int(42))]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(2)],
            vec![Instruction::Jump(SentenceIndex::from(0))]
        );
    }

    #[test]
    fn test_assemble_invalid_label() {
        let code = r#"
            sentence entry {
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
            
            sentence entry {
                push sym1
                push sym2
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 1);
        
        let sentence = &res.sentences[SentenceIndex::from(0)];
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
            test sentence my_test {
                push 1
                assert
            }
            export test sentence my_exported_test {
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

    #[test]
    fn test_assemble_arity_annotation() {
        let code = r#"
            #[arity(1, 2)]
            sentence with_arity {
                push 1
            }

            sentence without_arity {
                push 2
            }

            #[arity(3, 4)]
            export test sentence both_arity {
                push 3
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 3);

        let idx_with = SentenceIndex::from(0);
        let idx_without = SentenceIndex::from(1);
        let idx_both = SentenceIndex::from(2);

        assert_eq!(res.annotations[idx_with], vec![Annotation::Arity(1, 2)]);
        assert_eq!(res.annotations[idx_without], vec![]);
        assert_eq!(res.annotations[idx_both], vec![Annotation::Arity(3, 4)]);
    }

    #[test]
    fn test_arity_checker_errors() {
        // 1. Sentence requires more inputs than annotated
        let code = r#"
            #[arity(1, 1)]
            sentence bad_inputs {
                add
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("requires 2 inputs, which exceeds its annotated arity 1"));

        // 2. Net stack change is wrong
        let code = r#"
            #[arity(2, 2)]
            sentence bad_net_change {
                add
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("net stack change of -1, but annotated arity 2 -> 2 expects net change of 0"));

        // 3. Mismatched branch arities
        let code = r#"
            #[arity(0, 1)]
            sentence branch_then {
                push 1
            }
            #[arity(0, 2)]
            sentence branch_else {
                push 1
                push 2
            }
            #[arity(1, 1)]
            sentence bad_branch {
                branch branch_then branch_else
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Branch targets have mismatched net stack changes"));

        // 4. Recursion detected
        let code = r#"
            #[arity(0, 0)]
            sentence recursive_s {
                jump recursive_s
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Recursion/cycle detected"));
    }

    #[test]
    fn test_recursive_annotation_and_instruction_arities() {
        // 1. Recursive sentence annotated with #[recursive] compiles successfully
        let code = r#"
            #[recursive]
            sentence rec {
                jump rec
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 1);
        assert_eq!(res.instruction_arities[SentenceIndex::from(0)], None);

        // 2. Caller of recursive sentence must be annotated with #[recursive]
        let code2 = r#"
            #[recursive]
            sentence rec {
                jump rec
            }
            sentence caller {
                jump rec
            }
        "#;
        let res2 = assemble(code2);
        assert!(res2.is_err());
        assert!(res2.unwrap_err().contains("calls recursive sentence 'rec' but is not annotated with #[recursive]"));

        // 3. Verifying instruction arities are correctly populated for standard instructions
        let code3 = r#"
            sentence standard {
                push 10
                push 20
                add
                drop 0
            }
        "#;
        let res3 = assemble(code3).unwrap();
        assert_eq!(
            res3.instruction_arities[SentenceIndex::from(0)],
            Some(vec![
                Arity::Normal { inputs: 0, outputs: 0 },
                Arity::Normal { inputs: 0, outputs: 1 },
                Arity::Normal { inputs: 0, outputs: 2 },
                Arity::Normal { inputs: 0, outputs: 1 },
            ])
        );

        // 4. Verifying panic arity and _just_ panic sentence arity
        let code4 = r#"
            sentence just_panic {
                panic
            }
            #[arity(2, 0)]
            sentence annotated_panic {
                panic
            }
        "#;
        let res4 = assemble(code4).unwrap();
        assert_eq!(res4.instruction_arities[SentenceIndex::from(0)], Some(vec![Arity::Panic { inputs: 0 }]));
        assert_eq!(res4.instruction_arities[SentenceIndex::from(1)], Some(vec![Arity::Panic { inputs: 2 }]));
    }

    #[test]
    fn test_assemble_reserved_keywords() {
        let code = r#"
            mod crate {}
        "#;
        assert!(assemble(code).is_err());

        let code2 = r#"
            symbol super
        "#;
        assert!(assemble(code2).is_err());
    }

    #[test]
    fn test_assemble_duplicate_names() {
        let code = r#"
            symbol foo
            mod foo {}
        "#;
        assert!(assemble(code).is_err());
    }

    #[test]
    fn test_assemble_up_path_error() {
        let code = r#"
            sentence entry {
                jump super::entry
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("goes up too many levels"));
    }

    #[test]
    fn test_assemble_namespaces() {
        let code = r#"
            mod a {
                symbol my_sym "A's Symbol"
                mod b {
                    export test sentence my_test {
                        push super::my_sym
                        push crate::a::my_sym
                        equal
                        assert
                    }
                }
            }
        "#;
        let res = assemble(code).unwrap();
        assert!(res.tests.contains_key("a::b::my_test"));
        assert!(res.tests.contains_key("a::b::my_test"));
        assert!(res.exports.contains_key("a::b::my_test"));
    }

    #[test]
    fn test_assemble_file_mod_error_no_context() {
        let code = r#"
            mod my_external_file_module;
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("no base directory context was provided"));
    }

    #[test]
    fn test_assemble_file_mod_success() {
        let tmp_dir = std::env::temp_dir().join("hanoi_test_file_mods");
        let _ = std::fs::create_dir_all(&tmp_dir);
        
        let main_code = r#"
            mod helper;
            
            test sentence run {
                push helper::val
                push helper::val
                equal
                assert
            }
        "#;
        
        let helper_code = r#"
            symbol val "Helper Val"
        "#;
        
        std::fs::write(tmp_dir.join("helper.hana"), helper_code).unwrap();
        
        let res = assemble_with_path(main_code, Some(&tmp_dir)).unwrap();
        assert!(res.tests.contains_key("run"));
        
        let _ = std::fs::remove_file(tmp_dir.join("helper.hana"));
        let _ = std::fs::remove_dir(tmp_dir);
    }

    #[test]
    fn test_assemble_safety2_annotation() {
        let code = r#"
            #[arity(1, 1)]
            sentence safe_fn {
                drop 0
                push true
            }

            #[arity(1, 1)]
            #[safety2(safe_fn)]
            sentence my_func {
                drop 0
                push false
            }

            #[arity(1, 1)]
            #[safety2(super::safe_fn)]
            sentence other_func {
                drop 0
                push false
            }
        "#;
        let res = assemble(code).unwrap();
        let safe_fn_idx = res.names.iter().position(|n| n == "safe_fn").map(SentenceIndex::from).unwrap();
        let my_func_idx = res.names.iter().position(|n| n == "my_func").map(SentenceIndex::from).unwrap();
        let other_func_idx = res.names.iter().position(|n| n == "other_func").map(SentenceIndex::from).unwrap();

        assert_eq!(res.annotations[safe_fn_idx], vec![Annotation::Arity(1, 1)]);
        assert_eq!(
            res.annotations[my_func_idx],
            vec![Annotation::Arity(1, 1), Annotation::Safety2("safe_fn".to_string())]
        );
        assert_eq!(
            res.annotations[other_func_idx],
            vec![Annotation::Arity(1, 1), Annotation::Safety2("super::safe_fn".to_string())]
        );
    }
}
