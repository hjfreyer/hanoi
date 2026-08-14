pub mod arity;
pub mod assembly;
pub mod ast;
pub mod library;
pub mod lower;
pub mod opcode;
pub mod resolve;
pub mod source;
pub mod value;

pub use arity::check_arities;
pub use assembly::{assemble, assemble_source, assemble_with_path};
pub use library::{Annotation, Arity, Identity, IdentityIndex, Library, Sentence, SentenceIndex};
pub use opcode::Instruction;
pub use source::{Error, FileId, SourceMap, Span};
pub use value::{Symbol, Value};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_display() {
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Int(42)), "42");
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
                Instruction::Dip(SentenceIndex::from(1)),
            ]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Drop]
        );
    }

    /// The three coercions parse to themselves, and `as_tuple` takes its width.
    ///
    /// Each is one instruction with no expansion behind it, so the whole
    /// mnemonic table for them is what this pins down.
    #[test]
    fn the_coercions_assemble_to_one_instruction_each() {
        let res = assemble("sentence probe { as_bool as_int as_tuple 3 }").unwrap();
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![
                Instruction::AsBool,
                Instruction::AsInt,
                Instruction::AsTuple(3),
            ]
        );
        // One value in and one out, three times over, so the sentence reads
        // exactly the one value the first coercion needs.
        assert_eq!(
            arity::sentence_arity(&res, SentenceIndex::from(0)),
            Some(Arity {
                inputs: 1,
                outputs: 1
            })
        );
    }

    /// `as_tuple` without a width is refused rather than defaulted.
    ///
    /// A width is part of the type being coerced to — `dip`'s count defaults
    /// because one is the classic combinator, but there is no obvious tuple.
    #[test]
    fn as_tuple_needs_its_width() {
        assert!(assemble("sentence probe { as_tuple }").is_err());
    }

    // -----------------------------------------------------------------------
    // `?`
    // -----------------------------------------------------------------------

    /// The declarations `?` reads, in front of whatever the test is about.
    fn with_prelude(code: &str) -> String {
        format!("mod prelude {{ symbol ok symbol err }}\n{}", code)
    }

    fn blocks(library: &Library) -> Vec<&Sentence> {
        library
            .names
            .iter_enumerated()
            .filter(|(_, n)| *n == "<inline>")
            .map(|(i, _)| &library.sentences[i])
            .collect()
    }

    #[test]
    fn a_question_mark_becomes_two_branches_and_takes_the_rest_with_it() {
        let res = assemble(&with_prelude(
            "#[arity(1, 1)] sentence s { ? push 1 add drop 0 }",
        ))
        .unwrap();

        // The sentence itself is only the test: everything written after the
        // `?` moved into an arm.
        let [
            Instruction::Untuple(2),
            Instruction::Branch(is_ok, junk),
            Instruction::Branch(rest, fail),
        ] = res.sentences[SentenceIndex::from(0)][..]
        else {
            panic!(
                "expected the `?` expansion, got {:?}",
                res.sentences[SentenceIndex::from(0)]
            );
        };

        let ok = res.symbols["prelude::ok"].clone();
        let err = res.symbols["prelude::err"].clone();
        assert_eq!(
            res.sentences[is_ok],
            vec![Instruction::Push(ok), Instruction::Equal]
        );
        // A value that is not a 2-tuple answers `false` to "is this an ok?",
        // which is what makes `?` total on one.
        assert_eq!(
            res.sentences[junk],
            vec![Instruction::Drop, Instruction::Push(Value::Bool(false))]
        );
        assert_eq!(
            res.sentences[rest],
            vec![
                Instruction::Push(Value::Int(1)),
                Instruction::Add,
                Instruction::Drop
            ]
        );
        assert_eq!(
            res.sentences[fail],
            vec![Instruction::Push(err), Instruction::Tuple(2)]
        );
    }

    #[test]
    fn an_early_return_drops_what_the_rest_of_the_block_would_have_consumed() {
        // The rest arm is (2 -> 1): it eats the value the `?` unwrapped *and*
        // the one underneath. The early return eats only its own, so it drops
        // the difference from under the error it is carrying out.
        let res = assemble(&with_prelude("#[arity(2, 1)] sentence s { ? add drop 0 }")).unwrap();
        let [.., Instruction::Branch(_, fail)] = res.sentences[SentenceIndex::from(0)][..] else {
            panic!("expected the `?` expansion");
        };
        let err = res.symbols["prelude::err"].clone();
        let [
            Instruction::Push(ref e),
            Instruction::Tuple(2),
            Instruction::Dip(deep),
        ] = res.sentences[fail][..]
        else {
            panic!("expected one drop, got {:?}", res.sentences[fail]);
        };
        assert_eq!(*e, err);
        assert_eq!(res.sentences[deep], vec![Instruction::Drop]);
    }

    #[test]
    fn a_block_that_consumes_nothing_extra_needs_no_drops() {
        let res = assemble(&with_prelude("#[arity(1, 1)] sentence s { ? }")).unwrap();
        let [.., Instruction::Branch(rest, fail)] = res.sentences[SentenceIndex::from(0)][..]
        else {
            panic!("expected the `?` expansion");
        };
        assert!(
            res.sentences[rest].is_empty(),
            "nothing was written after it"
        );
        assert_eq!(
            res.sentences[fail].len(),
            2,
            "no drops: {:?}",
            res.sentences[fail]
        );
    }

    /// The count is measured, not guessed, so it follows a call whose arity is
    /// only known once every sentence has been emitted.
    #[test]
    fn the_drops_count_what_a_call_after_the_question_mark_consumes() {
        let res = assemble(&with_prelude(
            r#"
            #[arity(3, 1)] sentence s { ? jump eats }
            #[arity(3, 1)] sentence eats { add drop 0 add drop 0 }
        "#,
        ))
        .unwrap();
        let [.., Instruction::Branch(_, fail)] = res.sentences[SentenceIndex::from(0)][..] else {
            panic!("expected the `?` expansion");
        };
        assert_eq!(
            res.sentences[fail].len(),
            4,
            "two drops for the two extra values `eats` takes: {:?}",
            res.sentences[fail]
        );
    }

    #[test]
    fn a_nested_question_mark_is_balanced_before_the_one_around_it() {
        // Each `?` here has one value under it, so each early return drops one.
        // The outer one can only be measured once the inner one balances.
        let res = assemble(&with_prelude(
            r#"
            #[arity(3, 1)] sentence s { ? add drop 0 jump maybe ? add drop 0 }
            #[arity(1, 1)] sentence maybe { push crate::prelude::ok tuple 2 }
        "#,
        ))
        .unwrap();
        let with_drops = blocks(&res)
            .iter()
            .filter(|b| b.iter().any(|i| matches!(i, Instruction::Dip(_))))
            .count();
        assert_eq!(with_drops, 2, "both early returns drop");
    }

    #[test]
    fn a_question_mark_needs_the_tags_it_reads() {
        let err = assemble("sentence s { ? }").unwrap_err();
        assert!(err.contains("crate::prelude::ok"), "{}", err);
        assert!(
            err.contains("symbol ok"),
            "should say how to fix it: {}",
            err
        );
    }

    #[test]
    fn an_early_return_cannot_invent_what_the_rest_of_the_block_would_push() {
        let err = assemble(&with_prelude("sentence s { ? push 1 push 2 }")).unwrap_err();
        assert!(err.contains("leaves 2 more values"), "{}", err);
        assert!(err.contains("'s'"), "should name the sentence: {}", err);
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
    fn a_reach_at_depth_is_the_frames_it_stands_for() {
        // `pick 2` is `dip { pick 1 } ; swap`, and `pick 1` is
        // `dip { copy } ; swap` — the recursion written out, two nodes at every
        // depth but the bottom.
        let res = assemble("#[arity(3, 4)] sentence entry { pick 2 }").unwrap();
        let [Instruction::Dip(one), Instruction::Swap] = res.sentences[SentenceIndex::from(0)][..]
        else {
            panic!(
                "expected a frame and an exchange: {:?}",
                res.sentences[SentenceIndex::from(0)]
            )
        };
        let [Instruction::Dip(zero), Instruction::Swap] = res.sentences[one][..] else {
            panic!("expected the same one shallower: {:?}", res.sentences[one])
        };
        assert_eq!(res.sentences[zero], vec![Instruction::Copy]);
    }

    #[test]
    fn every_site_at_one_depth_shares_one_chain() {
        // The expansion costs `O(d)` blocks for the *program*, not for each
        // mention: what a reach stands for holds nothing from the site, so one
        // chain per (reach, depth) serves them all. Three `pick 4`s and a
        // `roll 4` cost the four blocks a single `pick 4` costs, plus the three
        // a `roll 4` needs — and the `roll` chain is not the `pick` chain,
        // since they differ at the bottom.
        let once = assemble("#[arity(5, 6)] sentence entry { pick 4 }")
            .unwrap()
            .sentences
            .len();
        let thrice = assemble("#[arity(5, 8)] sentence entry { pick 4 pick 4 pick 4 }")
            .unwrap()
            .sentences
            .len();
        assert_eq!(once, thrice, "a second mention should cost nothing");

        let mixed = assemble("#[arity(5, 6)] sentence entry { pick 4 roll 4 }")
            .unwrap()
            .sentences
            .len();
        assert_eq!(mixed, once + 3, "a roll bottoms out one level shallower");
    }

    #[test]
    fn test_assemble_dip() {
        let code = r#"
            #[arity(3, 3)]
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
            vec![Instruction::Dip(SentenceIndex::from(1))]
        );
        // `add` stands alone: the flag it leaves is the block's third output,
        // not something the assembler splices a drop in to remove.
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Add]
        );
    }

    #[test]
    fn test_assemble_dip_count_defaults_to_one() {
        let code = r#"
            #[arity(3, 3)]
            sentence entry {
                dip { add }
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(
            res.sentences[SentenceIndex::from(0)],
            vec![Instruction::Dip(SentenceIndex::from(1))]
        );
    }

    #[test]
    fn test_assemble_dip_to_label() {
        let code = r#"
            #[arity(2, 2)]
            sentence add_two {
                add
            }
            #[arity(4, 4)]
            sentence entry {
                dip 2 add_two
            }
        "#;
        let res = assemble(code).unwrap();
        // Two named sentences and the frame `dip 2` nests through: the outer
        // dip hides one value and calls a block that hides the second.
        assert_eq!(res.sentences.len(), 3);
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![Instruction::Dip(SentenceIndex::from(2))]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(2)],
            vec![Instruction::Dip(SentenceIndex::from(0))]
        );
    }

    #[test]
    fn test_dip_arity_counts_the_hidden_region() {
        // `dip 1 { add }` needs two values for the add plus one to hide, and
        // leaves the hidden value on top of the sum and its flag.
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
            #[arity(3, 3)]
            sentence good_dip {
                dip { add }
            }
        "#;
        assert!(assemble(code).is_ok());
    }

    #[test]
    fn test_dip_through_a_cycle_is_rejected() {
        let code = r#"
            sentence loops {
                dip { jump loops }
            }
        "#;
        let res = assemble(code);
        assert!(res.unwrap_err().contains("reaches itself"));
    }

    #[test]
    fn test_assemble_nested_branching() {
        let code = r#"
            sentence elsewhere {
                push 7
            }
            sentence entry {
                push true
                branch {
                    push 42
                } {
                    jump elsewhere
                }
            }
        "#;
        let res = assemble(code).unwrap();
        // Should have compiled 4 sentences:
        // Index 0: elsewhere
        // Index 1: entry
        // Index 2: inline true block
        // Index 3: inline false block
        assert_eq!(res.sentences.len(), 4);
        assert_eq!(
            res.sentences[SentenceIndex::from(1)],
            vec![
                Instruction::Push(Value::Bool(true)),
                Instruction::Branch(SentenceIndex::from(2), SentenceIndex::from(3)),
            ]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(2)],
            vec![Instruction::Push(Value::Int(42))]
        );
        assert_eq!(
            res.sentences[SentenceIndex::from(3)],
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
            symbol sym1
            mod m {
                symbol sym2
            }

            sentence entry {
                push sym1
                push m::sym2
            }
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 1);

        let sentence = &res.sentences[SentenceIndex::from(0)];
        assert_eq!(sentence.len(), 2);

        // Assert sym1 and sym2 are distinct symbols, each carrying the fully
        // qualified name it was declared under.
        if let (Instruction::Push(Value::Symbol(s1)), Instruction::Push(Value::Symbol(s2))) =
            (&sentence[0], &sentence[1])
        {
            assert_ne!(s1, s2);
            assert_eq!(s1.path, "sym1");
            assert_eq!(s2.path, "m::sym2");
        } else {
            panic!("Expected pushing of two symbols");
        }
    }

    #[test]
    fn a_symbol_prints_as_the_path_it_was_declared_under() {
        let code = r#"
            mod m {
                symbol s
            }
            sentence entry {
                push m::s
            }
        "#;
        let res = assemble(code).unwrap();
        let Instruction::Push(sym) = &res.sentences[SentenceIndex::from(0)][0] else {
            panic!("expected a push");
        };
        assert_eq!(sym.to_string(), "m::s");
    }

    #[test]
    fn test_assemble_const_strings() {
        // A const string is its text: two declarations reading the same are
        // the same value, which is the whole difference from a symbol.
        let code = r#"
            const_string greeting "hello"
            const_string other "hello"

            sentence entry {
                push greeting
                push other
                push "hello"
            }
        "#;
        let res = assemble(code).unwrap();
        let sentence = &res.sentences[SentenceIndex::from(0)];
        let expected = Instruction::Push(Value::ConstString("hello".to_string()));
        assert_eq!(
            sentence,
            &vec![expected.clone(), expected.clone(), expected]
        );

        // Const strings are not symbols, so nothing needs to look one up by
        // name at runtime.
        assert!(res.symbols.is_empty());
    }

    #[test]
    fn a_const_string_declaration_needs_its_text() {
        let err = assemble("const_string greeting").unwrap_err();
        assert!(err.contains("expected a string literal"), "{}", err);
    }

    #[test]
    fn a_symbol_declaration_refuses_the_text_it_used_to_carry() {
        // The one migration worth naming: the description a symbol used to
        // take was also the text `symbol_len` read, and both are now the
        // business of `const_string`.
        let err = assemble(r#"symbol greeting "hello""#).unwrap_err();
        assert!(err.contains("a symbol carries no text"), "{}", err);
        assert!(err.contains(r#"const_string greeting "hello""#), "{}", err);
    }

    #[test]
    fn a_const_string_survives_a_composer_template() {
        // Composer templates are rendered as text and re-parsed, so a value
        // passed to one has to print as something that lexes back to it. A
        // string literal is the only value where that takes quoting.
        let code = r#"
            mod m {
                export function init { drop 0 push "unused" }
                export function accept { drop 0 push false }
                export function tau_reduce { push false tuple 2 }
                export function emit { drop 0 tuple 0 push false tuple 2 }
                export function process { untuple 2 drop 0 drop 0 }
                export function is_done { drop 0 push false }
                export function is_ready_to_finish { drop 0 push false }
            }
            mod closed compose_static_closure(m, "xyz");
        "#;
        let res = assemble(code).unwrap();
        let idx = res.names.iter().position(|n| n == "closed::init").unwrap();
        assert!(
            res.sentences[SentenceIndex::from(idx)]
                .contains(&Instruction::Push(Value::ConstString("xyz".to_string()))),
            "{:?}",
            res.sentences[SentenceIndex::from(idx)]
        );
    }

    #[test]
    fn test_assemble_test_annotation() {
        let code = r#"
            test sentence my_test {
                push 1
                drop 0
            }
            export test sentence my_exported_test {
                push 2
                drop 0
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
            #[arity(2, 1)]
            sentence bad_net_change {
                add
            }
        "#;
        let res = assemble(code);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains(
            "net stack change of 0, but annotated arity 2 -> 1 expects net change of -1"
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
            sentence loops {
                jump loops
            }
        "#;
        let res = assemble(code);
        assert!(res.unwrap_err().contains("reaches itself"));
    }

    /// Recursion is forbidden, and inference is what forbids it: a sentence
    /// that reaches itself has no arity to work out. Every way of writing a
    /// cycle goes through the same check, whether the call is a `jump`, a
    /// `dip`, or a branch arm, and whether the sentence names itself or comes
    /// back round through another.
    #[test]
    fn test_every_spelling_of_a_cycle_is_refused() {
        for code in [
            "sentence loops { jump loops }",
            "sentence ping { jump pong } sentence pong { jump ping }",
            "sentence viabranch { pick 0 branch { drop 0 } { jump viabranch } }",
            "sentence entry { jump loops } sentence loops { jump loops }",
        ] {
            let res = assemble(code);
            assert!(
                res.as_ref()
                    .is_err_and(|e| e.contains("recursion is forbidden")),
                "expected {:?} to be refused, got {:?}",
                code,
                res.map(|_| ())
            );
        }
    }

    /// The annotation that used to license recursion says so itself, rather
    /// than coming back as a name that might have been misspelled.
    #[test]
    fn test_the_recursive_annotation_is_gone() {
        let err = assemble("#[recursive] sentence s { push 1 }").unwrap_err();
        assert!(err.contains("recursion is forbidden"), "{}", err);
    }

    #[test]
    fn test_instruction_arities() {
        // 1. Verifying instruction arities are correctly populated for standard instructions
        let code3 = r#"
            sentence standard {
                push 10
                push 20
                add
                drop 0
            }
        "#;
        let res3 = assemble(code3).unwrap();
        // One entry per written instruction, each the arity of the prefix
        // before it. `add` is fallible and the sentence keeps its flag, so the
        // depth stays at 2 across it and the `drop 0` takes it back to 1.
        assert_eq!(
            res3.instruction_arities[SentenceIndex::from(0)],
            vec![
                Arity {
                    inputs: 0,
                    outputs: 0
                },
                Arity {
                    inputs: 0,
                    outputs: 1
                },
                Arity {
                    inputs: 0,
                    outputs: 2
                },
                Arity {
                    inputs: 0,
                    outputs: 2
                },
            ]
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
                        drop 0
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
                symbol my_sym
                mod b {
                    export test sentence my_test {
                        push super::my_sym
                        push crate::a::my_sym
                        equal
                        drop 0
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
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot load external module `my_external_file_module`"),
            "{}",
            err
        );
        // The module name is what gets underlined, not the whole declaration.
        assert!(err.contains("--> <input>:2:17"), "{}", err);
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
                drop 0
            }
        "#;

        let helper_code = r#"
            symbol val
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
        assert!(res.unwrap_err().contains("duplicate #[precondition]"));

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
        assert!(res2.unwrap_err().contains("duplicate #[postcondition]"));

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

    /// The annotation that claimed a sentence could not fail says what became
    /// of it, rather than coming back as a name that might be misspelled.
    #[test]
    fn test_the_total_annotation_is_gone() {
        let err = assemble("#[total] sentence s { push 1 }").unwrap_err();
        assert!(err.contains("nothing can fail"), "{}", err);
    }

    #[test]
    fn test_type_definitions_primitives() {
        let code = r#"
            type MyInt int;
            type MyBool bool;
            type MySymbol symbol;
            type MyTuple tuple;
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 4);

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
            type Nested (IntOrBool, Pair | symbol);
            type Empty ();
        "#;
        let res = assemble(code).unwrap();
        // A tuple spec is one `untuple` and a branch, so it contributes two
        // arms rather than the four the old `is_tuple`/`tuple_length` guards
        // nested. `Empty` contributes none at all: `untuple 0` leaves exactly
        // the answer. Each tuple spec past its first element still contributes
        // one dip block, which is flattened into a sentence of its own: one for
        // `Pair`, one for `Nested`.
        assert_eq!(res.sentences.len(), 14);
    }

    #[test]
    fn test_generated_type_checks_contain_no_roll() {
        // Element checks are dipped under the accumulated result rather than
        // rolled around it, so lowering no longer emits any roll at all — and
        // `swap` is what a roll expands to, so it is what there should be none
        // of once the depths have been compiled away.
        let code = r#"
            type Triple (int, bool, symbol);
            type Nested (int, (bool, tuple), symbol);
            enum E { A(int, bool), B(symbol, symbol, int) }
        "#;
        let res = assemble(code).unwrap();
        for sentence in res.sentences.iter() {
            assert!(
                !sentence.iter().any(|i| matches!(i, Instruction::Swap)),
                "generated check should contain no roll: {:?}",
                sentence
            );
        }
    }

    #[test]
    fn test_type_definitions_literals() {
        let code = r#"
            symbol my_sym
            type OnlySym my_sym;
            type Only42 42;
            type TrueOrHi true | "hi";
        "#;
        let res = assemble(code).unwrap();
        assert_eq!(res.sentences.len(), 5);
    }
}
