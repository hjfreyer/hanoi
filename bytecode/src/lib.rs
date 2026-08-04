pub mod arity;
pub mod assembly;
pub mod ast;
pub mod library;
pub mod lower;
pub mod opcode;
pub mod resolve;
pub mod value;

pub use arity::{check_arities, check_totality, failure_reachability};
pub use assembly::{assemble, assemble_with_path};
pub use library::{Annotation, Arity, Library, Sentence, SentenceIndex};
pub use opcode::Instruction;
pub use value::{Symbol, Value};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_display() {
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::Float(1.5)), "1.5");
    }

    #[test]
    fn test_instruction_equality() {
        let inst1 = Instruction::Push(Value::Int(42));
        let inst2 = Instruction::Push(Value::Int(42));
        let inst3 = Instruction::Drop;

        assert_eq!(inst1, inst2);
        assert_ne!(inst1, inst3);
    }

    #[test]
    fn test_library_indexing() {
        let mut library = Library::new();
        let sentence1 = vec![Instruction::Push(Value::Int(10)), Instruction::Drop];
        let sentence2 = vec![Instruction::Push(Value::Int(20)), Instruction::Drop];

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
        // `drop 1` expands into a dip around a plain drop, which gets its own
        // sentence.
        assert_eq!(res.sentences.len(), 2);
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![
                Instruction::Push(Value::Int(42)),
                Instruction::Push(Value::Tuple(vec![
                    Value::Int(1),
                    Value::Int(2),
                    Value::Tuple(vec![Value::Int(3), Value::Bool(false)])
                ])),
                Instruction::Dip(1, SentenceIndex::from(1)),
            ]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Drop]
        );
    }

    #[test]
    fn test_drop_zero_does_not_expand() {
        let code = r#"
            #[arity(1, 0)]
            sentence entry {
                drop 0
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 1);
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![Instruction::Drop]
        );
    }

    #[test]
    fn test_assemble_dip() {
        let code = r#"
            #[arity(3, 2)]
            sentence entry {
                dip 1 {
                    add
                }
            }
        "#;
        let res = assemble(code).unwrap();
        // The inline block is flattened into its own sentence, as for branch.
        assert_eq!(res.sentences.len(), 2);
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![Instruction::Dip(1, SentenceIndex::from(1))]
        );
        // `add` is fallible, so it leaves a success flag; without `#[flags]`
        // the assembler drops it right there and the block's effect on the
        // stack is what it always was.
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Add, Instruction::Drop]
        );
    }

    #[test]
    fn test_assemble_dip_count_defaults_to_one() {
        let code = r#"
            #[arity(3, 2)]
            sentence entry {
                dip { add }
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![Instruction::Dip(1, SentenceIndex::from(1))]
        );
    }

    #[test]
    fn test_assemble_dip_to_label() {
        let code = r#"
            #[arity(2, 1)]
            sentence add_two {
                add
            }
            #[arity(4, 3)]
            sentence entry {
                dip 2 add_two
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 2);
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Dip(2, SentenceIndex::from(0))]
        );
    }

    #[test]
    fn test_dip_arity_counts_the_hidden_region() {
        // `dip 1 { add }` needs two values for the add plus one to hide, and
        // leaves the hidden value on top of the sum.
        let code = r#"
            #[arity(1, 1)]
            sentence bad_dip {
                dip { add }
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(
            res.unwrap_err()
                .contains("requires 3 inputs, which exceeds its annotated arity 1")
        );

        // The same body checks out against the arity it actually has.
        let code = r#"
            #[arity(3, 2)]
            sentence good_dip {
                dip { add }
            }
        "#;
        assert!(assemble(code).is_ok());
    }

    #[test]
    fn test_dip_through_recursive_target_is_rejected() {
        let code = r#"
            #[recursive]
            sentence loops {
                dip { jump loops }
            }
            #[arity(2, 2)]
            sentence caller {
                dip { jump loops }
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(
            res.unwrap_err()
                .contains("but is not annotated with #[recursive]")
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
            vec![Instruction::Dip(0, SentenceIndex::from(0))]
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
        if let (Instruction::Push(Value::Symbol(s1)), Instruction::Push(Value::Symbol(s2))) =
            (&sentence[0], &sentence[1])
        {
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
        assert_eq!(
            res.tests.get("my_exported_test"),
            Some(&SentenceIndex::from(1))
        );
        assert_eq!(
            res.exports.get("my_exported_test"),
            Some(&SentenceIndex::from(1))
        );
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
        assert!(
            res.unwrap_err()
                .contains("requires 2 inputs, which exceeds its annotated arity 1")
        );

        // 2. Net stack change is wrong
        let code = r#"
            #[arity(2, 2)]
            sentence bad_net_change {
                add
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains(
            "net stack change of -1, but annotated arity 2 -> 2 expects net change of 0"
        ));

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
        assert!(
            res.unwrap_err()
                .contains("Branch targets have mismatched net stack changes")
        );

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
        assert!(
            res2.unwrap_err()
                .contains("calls recursive sentence 'rec' but is not annotated with #[recursive]")
        );

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
        // Five instructions for four written: `add` is fallible and its flag is
        // dropped on the spot, so the depth goes 2 -> 2 -> 1 rather than
        // 2 -> 1.
        assert_eq!(
            res3.instruction_arities[SentenceIndex::from(0)],
            Some(vec![
                Arity::Normal {
                    inputs: 0,
                    outputs: 0
                },
                Arity::Normal {
                    inputs: 0,
                    outputs: 1
                },
                Arity::Normal {
                    inputs: 0,
                    outputs: 2
                },
                Arity::Normal {
                    inputs: 0,
                    outputs: 2
                },
                Arity::Normal {
                    inputs: 0,
                    outputs: 1
                },
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
        assert_eq!(
            res4.instruction_arities[SentenceIndex::from(0)],
            Some(vec![Arity::Panic { inputs: 0 }])
        );
        assert_eq!(
            res4.instruction_arities[SentenceIndex::from(1)],
            Some(vec![Arity::Panic { inputs: 2 }])
        );
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
        let res = assemble(code);
        assert!(res.is_err());
        assert!(
            res.unwrap_err()
                .contains("Duplicate declaration of name 'foo'")
        );

        // Symbols, sentences and modules share one namespace, so a sentence
        // collides with a symbol of the same name too.
        let code2 = r#"
            symbol foo
            sentence foo {}
        "#;
        assert!(assemble(code2).is_err());
    }

    #[test]
    fn test_assemble_path_resolution_errors() {
        // A module is not an item: it can be navigated through, not pushed.
        let code = r#"
            mod m { symbol s }
            sentence entry {
                push m
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("names a module"));

        // A non-module cannot appear as an intermediate segment.
        let code2 = r#"
            symbol s
            sentence entry {
                push s::inner
            }
        "#;
        let res2 = assemble(code2);
        assert!(res2.is_err());
        assert!(res2.unwrap_err().contains("is a symbol, not a module"));

        // 'crate' and 'super' are only meaningful as a path prefix.
        let code3 = r#"
            mod a { symbol s }
            sentence entry {
                push a::crate
            }
        "#;
        let res3 = assemble(code3);
        assert!(res3.is_err());
        assert!(
            res3.unwrap_err()
                .contains("'crate' can only appear at the beginning")
        );

        let code4 = r#"
            mod a { mod b { symbol s } }
            sentence entry {
                push crate::a::super::b
            }
        "#;
        let res4 = assemble(code4);
        assert!(res4.is_err());
        assert!(
            res4.unwrap_err()
                .contains("'super' can only appear at the beginning")
        );
    }

    #[test]
    fn test_assemble_super_run_resolves_through_ancestors() {
        let code = r#"
            symbol s
            mod a {
                mod b {
                    export test sentence entry {
                        push super::super::s
                        push crate::s
                        equal
                        assert
                    }
                }
            }
        "#;
        let res = assemble(code).unwrap();
        assert!(res.tests.contains_key("a::b::entry"));
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
        assert!(
            res.unwrap_err()
                .contains("no base directory context was provided")
        );
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

    fn sentence_named(lib: &Library, name: &str) -> SentenceIndex {
        lib.names
            .iter()
            .position(|n| n == name)
            .map(SentenceIndex::from)
            .unwrap_or_else(|| panic!("no sentence named '{}'", name))
    }

    #[test]
    fn test_assemble_precondition_annotation() {
        // Contract paths resolve against the module the annotated sentence is
        // declared in, so `inner` reaches its parent's `safe_fn` with `super::`.
        let code = r#"
            function safe_fn {
                drop 0
                push true
            }

            #[precondition(safe_fn)]
            function my_func {
                drop 0
                push false
            }

            mod inner {
                #[precondition(super::safe_fn)]
                function other_func {
                    drop 0
                    push false
                }
            }
        "#;
        let res = assemble(code).unwrap();
        let safe_fn_idx = sentence_named(&res, "safe_fn");

        assert_eq!(res.annotations[safe_fn_idx], vec![Annotation::Arity(1, 1)]);
        assert_eq!(
            res.annotations[sentence_named(&res, "my_func")],
            vec![
                Annotation::Precondition(safe_fn_idx),
                Annotation::Arity(1, 1)
            ]
        );
        assert_eq!(
            res.annotations[sentence_named(&res, "inner::other_func")],
            vec![
                Annotation::Precondition(safe_fn_idx),
                Annotation::Arity(1, 1)
            ]
        );
    }

    #[test]
    fn test_assemble_contract_annotation_errors() {
        // Unresolvable target.
        let code = r#"
            #[precondition(nope)]
            function my_func {
                drop 0
                push false
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("unresolved precondition 'nope'"));

        // A contract must name a sentence, not a symbol.
        let code2 = r#"
            symbol s
            #[postcondition(s)]
            function my_func {
                drop 0
                push false
            }
        "#;
        let res2 = assemble(code2);
        assert!(res2.is_err());
        assert!(
            res2.unwrap_err()
                .contains("names a symbol, but must name a sentence")
        );

        // `super::` from the crate root walks off the top of the tree. This used
        // to be stored verbatim and only fail later, if the typechecker ran.
        let code3 = r#"
            function safe_fn {
                drop 0
                push true
            }
            #[precondition(super::safe_fn)]
            function my_func {
                drop 0
                push false
            }
        "#;
        let res3 = assemble(code3);
        assert!(res3.is_err());
        assert!(res3.unwrap_err().contains("goes up too many levels"));
    }

    #[test]
    fn test_assemble_rejects_duplicate_contracts() {
        // Verification reads one precondition and one postcondition, so a second
        // would be silently dropped rather than conjoined.
        let code = r#"
            function a { drop 0 push true }
            function b { drop 0 push true }

            #[precondition(a)]
            #[precondition(b)]
            function my_func {
                drop 0
                push false
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Duplicate #[precondition]"));

        let code2 = r#"
            function a { drop 0 push true }
            function b { drop 0 push true }

            #[postcondition(a)]
            #[postcondition(b)]
            function my_func {
                drop 0
                push false
            }
        "#;
        let res2 = assemble(code2);
        assert!(res2.is_err());
        assert!(res2.unwrap_err().contains("Duplicate #[postcondition]"));

        // One of each is fine, and `arity` may still repeat: every one is checked.
        let code3 = r#"
            function a { drop 0 push true }

            #[precondition(a)]
            #[postcondition(a)]
            #[arity(1, 1)]
            sentence my_func {
                drop 0
                push false
            }
        "#;
        assert!(assemble(code3).is_ok());
    }

    #[test]
    fn test_assemble_postcondition_annotation() {
        let code = r#"
            function post_fn {
                drop 0
                push true
            }

            #[postcondition(post_fn)]
            function my_func {
                drop 0
                push false
            }

            mod inner {
                #[postcondition(super::post_fn)]
                function other_func {
                    drop 0
                    push false
                }
            }
        "#;
        let res = assemble(code).unwrap();
        let post_fn_idx = sentence_named(&res, "post_fn");

        assert_eq!(res.annotations[post_fn_idx], vec![Annotation::Arity(1, 1)]);
        assert_eq!(
            res.annotations[sentence_named(&res, "my_func")],
            vec![
                Annotation::Postcondition(post_fn_idx),
                Annotation::Arity(1, 1)
            ]
        );
        assert_eq!(
            res.annotations[sentence_named(&res, "inner::other_func")],
            vec![
                Annotation::Postcondition(post_fn_idx),
                Annotation::Arity(1, 1)
            ]
        );
    }

    #[test]
    fn test_assemble_total_annotation() {
        let code = r#"
            #[total]
            function my_func {
                drop 0
                push false
            }
        "#;
        let res = assemble(code).unwrap();
        let my_func_idx = res
            .names
            .iter()
            .position(|n| n == "my_func")
            .map(SentenceIndex::from)
            .unwrap();

        assert_eq!(
            res.annotations[my_func_idx],
            vec![Annotation::Total, Annotation::Arity(1, 1)]
        );
    }

    #[test]
    fn test_type_definitions_primitives() {
        let code = r#"
            type MyInt int;
            type MyBool bool;
            type MyFloat float;
            type MySymbol symbol;
            type MyTuple tuple;
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 5);

        for idx in 0..5 {
            let s_idx = SentenceIndex::from(idx);
            assert!(res.annotations[s_idx].contains(&Annotation::Total));
        }

        // uppercase 'Int' should fail because it is case-sensitive
        let bad_code = r#"
            type BadInt Int;
        "#;
        assert!(assemble(bad_code).is_err());
    }

    #[test]
    fn test_type_definitions_unions_and_tuples() {
        let code = r#"
            type IntOrBool int | bool;
            type Pair (int, bool);
            type Nested (IntOrBool, Pair | float);
            type Empty ();
        "#;
        let res = assemble(code).unwrap();
        // Each tuple spec past its first element contributes one dip block,
        // which is flattened into a sentence of its own: one for `Pair`, one
        // for `Nested`.
        assert_eq!(res.sentences.len(), 22);
    }

    #[test]
    fn test_generated_type_checks_contain_no_roll() {
        // Element checks are dipped under the accumulated result rather than
        // rolled around it, so lowering no longer emits any roll at all.
        let code = r#"
            type Triple (int, bool, float);
            type Nested (int, (bool, float), symbol);
            enum E { A(int, bool), B(symbol, symbol, int) }
        "#;
        let res = assemble(code).unwrap();
        for sentence in res.sentences.iter() {
            assert!(
                !sentence.iter().any(|i| matches!(i, Instruction::Roll(_))),
                "generated check should contain no roll: {:?}",
                sentence
            );
        }
    }

    #[test]
    fn test_type_definitions_literals() {
        let code = r#"
            symbol my_sym "some symbol"
            type OnlySym my_sym;
            type Only42 42;
            type TrueOr314 true | 3.14;
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 5);
    }
}
