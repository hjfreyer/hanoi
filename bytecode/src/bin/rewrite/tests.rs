//! Tests for the rewrite tool.

use std::collections::HashSet;

use bytecode::{assemble, SentenceIndex};
use std::fs;
use std::path::Path;

use crate::arity::{node_arity, seq_arity};
use crate::ir::{build, Node};
use crate::passes::{expand_to_unary_dips, rewrite, Passes};

const DIPS: Passes = Passes {
    dip_normalize: true,
    factor_branches: false,
    annihilate: false,
};

const FACTOR: Passes = Passes {
    dip_normalize: false,
    factor_branches: true,
    annihilate: false,
};

const ANNIHILATE: Passes = Passes {
    dip_normalize: false,
    factor_branches: false,
    annihilate: true,
};

const ALL: Passes = Passes {
    dip_normalize: true,
    factor_branches: true,
    annihilate: true,
};

/// Net stack change, which every pass must preserve exactly.
fn net(nodes: &[Node]) -> Option<i64> {
    let (inputs, outputs) = seq_arity(nodes);
    outputs.map(|o| o - inputs)
}

fn tree(code: &str, passes: Passes) -> Vec<Node> {
    let library = assemble(code).unwrap();
    let mut body = build(&library, SentenceIndex::from(0), &mut HashSet::new());
    rewrite(&mut body, passes);
    body
}

/// The depth before each instruction of a sequence, entered at its inputs.
fn depths(nodes: &[Node]) -> Vec<Option<i64>> {
    let mut depth = Some(seq_arity(nodes).0);
    let mut out = Vec::new();
    for node in nodes {
        out.push(depth);
        depth = match (depth, node_arity(node)) {
            (Some(d), Some((n, m))) => Some(d - n + m),
            _ => None,
        };
    }
    out
}

fn shape(nodes: &[Node]) -> Vec<String> {
    nodes
        .iter()
        .map(|node| match node {
            Node::Op(inst) => format!("{}", inst),
            Node::Dip { depth, body, .. } => {
                format!("dip {} {{ {} }}", depth, shape(body).join(" "))
            }
            Node::Branch { .. } => "branch".to_string(),
            Node::Cut(_) => "cut".to_string(),
        })
        .collect()
}

#[test]
fn depth_counts_inputs_once() {
    // Regression: an earlier version read the arity checker's recorded
    // per-instruction size, which already includes the inputs found so far,
    // and added the total back on — reporting `is_tuple` one deeper than it
    // runs.
    let body = tree(
        r#"
        #[arity(1, 1)]
        sentence probe {
            pick 0
            is_tuple
            and
        }
    "#,
        Passes::default(),
    );
    assert_eq!(depths(&body), vec![Some(1), Some(2), Some(2)]);
}

#[test]
fn dip_contributes_only_its_targets_net_change() {
    let body = tree(
        r#"
        #[arity(3, 1)]
        sentence probe {
            dip 1 { add }
            drop 0
        }
    "#,
        Passes::default(),
    );
    assert_eq!(depths(&body), vec![Some(3), Some(2)]);
    // The dip itself takes three and leaves two: two consumed by the add,
    // plus the one it holds out of the way.
    assert_eq!(node_arity(&body[0]), Some((3, 2)));
}

#[test]
fn depth_stops_being_known_after_a_panic() {
    let body = tree(
        r#"
        #[arity(0, 0)]
        sentence probe {
            push 1
            panic
            push 2
        }
    "#,
        Passes::default(),
    );
    assert_eq!(depths(&body), vec![Some(0), Some(1), None]);
}

#[test]
fn factoring_looks_past_provenance() {
    // Both arms open with the same dipped block. They are separate inline
    // sentences, so they carry different labels — but the labels are for
    // the listing, not for deciding what the code does, and the prefix has
    // to factor anyway.
    let body = tree(
        r#"
        sentence probe {
            branch { dip 1 { add } push 1 } { dip 1 { add } push 2 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(
        shape(&body),
        vec!["dip 1 { dip 1 { add } }", "branch"],
        "the shared dipped prefix should have been hoisted"
    );
}

#[test]
fn a_cycle_has_no_static_arity() {
    let body = tree(
        r#"
        #[recursive]
        sentence loops {
            push 1
            jump loops
        }
    "#,
        Passes::default(),
    );
    assert_eq!(seq_arity(&body).1, None);
}

#[test]
fn dips_sink_past_pushes_and_arithmetic() {
    // The dip starts at the end hiding one value. Moving it past `add`
    // widens it to two operands, and past each push narrows it again, so it
    // arrives at the front hiding nothing at all.
    let body = tree(
        r#"
        #[arity(2, 2)]
        sentence probe {
            push 1
            push 2
            add
            dip 1 { add }
        }
    "#,
        DIPS,
    );
    assert_eq!(
        shape(&body),
        vec!["dip 0 { add }", "push 1", "push 2", "add"]
    );
}

#[test]
fn dips_fuse_when_they_meet_at_the_same_depth() {
    let body = tree(
        r#"
        #[arity(3, 3)]
        sentence probe {
            dip 1 { pick 0 drop 0 }
            dip 1 { pick 0 drop 0 }
        }
    "#,
        DIPS,
    );
    assert_eq!(
        shape(&body),
        vec!["dip 1 { pick 0 drop pick 0 drop }"]
    );
}

fn tree_unary(code: &str) -> Vec<Node> {
    let mut body = tree(code, DIPS);
    expand_to_unary_dips(&mut body);
    body
}

#[test]
fn a_deep_dip_becomes_a_nest_of_unary_dips() {
    // `untuple 3` leaves three values, so a dip hiding two cannot clear it
    // and stays put — which is what makes this a case where the expansion
    // has something to do.
    let body = tree_unary(
        r#"
        sentence probe {
            untuple 3
            dip 2 { add }
        }
    "#,
    );
    assert_eq!(
        shape(&body),
        vec!["untuple 3", "dip 1 { dip 1 { add } }"]
    );
}

#[test]
fn expansion_leaves_plain_calls_alone() {
    // `dip 0` hides nothing, so there is no unary nest to write it as.
    let body = tree_unary(
        r#"
        sentence probe {
            push 1
            push 2
            dip 0 { add }
        }
    "#,
    );
    assert_eq!(shape(&body), vec!["push 1", "push 2", "dip 0 { add }"]);
}

#[test]
fn expansion_preserves_arity() {
    let code = r#"
        sentence probe {
            untuple 3
            dip 2 { add }
        }
    "#;
    let normalized = tree(code, DIPS);
    let unary = tree_unary(code);
    assert_ne!(shape(&normalized), shape(&unary), "expected an expansion");
    assert_eq!(seq_arity(&normalized), seq_arity(&unary));
}

#[test]
fn nested_dips_collapse_and_then_keep_sinking() {
    // Hiding one and then one more is hiding two, and once that is a single
    // dip it sinks past both of the pushes it was reaching over.
    //
    // It stops at `push 2`: by then it has narrowed to `dip 0`, which is a
    // plain call taking its argument off the top — exactly the value that
    // push put there. That is the rule's `k >= m` biting, and it is the
    // point at which the dip has reached the values it actually operates on.
    let body = tree(
        r#"
        sentence probe {
            push 1
            push 2
            push 8
            push 9
            dip 1 { dip 1 { add } }
        }
    "#,
        DIPS,
    );
    assert_eq!(
        shape(&body),
        vec!["push 1", "push 2", "dip 0 { add }", "push 8", "push 9"]
    );
}

#[test]
fn fusing_records_every_origin() {
    let library = assemble(
        r#"
        sentence probe {
            push 1
            push 2
            push 8
            push 9
            dip 1 { dip 1 { add } }
        }
    "#,
    )
    .unwrap();
    let mut body = build(&library, SentenceIndex::from(0), &mut HashSet::new());
    rewrite(&mut body, DIPS);

    let origins = body
        .iter()
        .find_map(|node| match node {
            Node::Dip { origins, .. } => Some(origins),
            _ => None,
        })
        .expect("a dip should survive normalization");
    // Both of the sentences that were collapsed together are named, so the
    // listing still says where the merged block came from.
    assert_eq!(origins.len(), 2);
}

#[test]
fn a_dip_stops_at_a_pick_that_reaches_into_it() {
    // `pick 2` reads three deep, so a dip hiding only one value would be
    // rewriting the very slot the pick copies from. It has to stay put.
    let body = tree(
        r#"
        sentence probe {
            pick 2
            dip 1 { pick 0 }
        }
    "#,
        DIPS,
    );
    assert_eq!(shape(&body), vec!["pick 2", "dip 1 { pick 0 }"]);
}

#[test]
fn a_dip_sinks_past_a_pick_it_clears() {
    // Same shape, but hiding four values puts the whole pick above the
    // window, so the move is sound.
    let body = tree(
        r#"
        sentence probe {
            pick 2
            dip 4 { pick 0 }
        }
    "#,
        DIPS,
    );
    assert_eq!(shape(&body), vec!["dip 3 { pick 0 }", "pick 2"]);
}

#[test]
fn a_shared_branch_prefix_is_hoisted_under_a_dip() {
    // The `push 7` runs either way, so it can run before the condition is
    // consumed — under a dip, since the condition is still on top.
    let body = tree(
        r#"
        sentence probe {
            branch { push 7 push 1 } { push 7 push 2 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(shape(&body), vec!["dip 1 { push 7 }", "branch"]);
}

#[test]
fn factoring_takes_the_whole_shared_run() {
    let body = tree(
        r#"
        sentence probe {
            branch { push 7 is_int push 1 } { push 7 is_int push 2 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(shape(&body), vec!["dip 1 { push 7 is_int }", "branch"]);
}

#[test]
fn factoring_stops_where_the_arms_diverge() {
    // Both arms also end with `push 5`, but only the prefix is hoistable:
    // what runs before the branch has to run before *both* arms, and the
    // trailing pushes are separated by instructions that differ.
    let body = tree(
        r#"
        sentence probe {
            branch { push 7 push 1 push 5 } { push 7 push 2 push 5 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(shape(&body), vec!["dip 1 { push 7 }", "branch"]);
    let Node::Branch {
        then_body,
        else_body,
        ..
    } = &body[1]
    else {
        panic!("expected a branch")
    };
    assert_eq!(shape(then_body), vec!["push 1", "push 5"]);
    assert_eq!(shape(else_body), vec!["push 2", "push 5"]);
}

#[test]
fn a_push_and_a_drop_cancel() {
    let body = tree(
        r#"
        sentence probe {
            push 1
            push 2
            drop 0
            drop 0
        }
    "#,
        ANNIHILATE,
    );
    // Cancelling the inner pair exposes the outer one.
    assert!(body.is_empty(), "expected nothing left, got {:?}", shape(&body));
}

#[test]
fn a_pick_and_a_drop_cancel() {
    let body = tree(
        r#"
        sentence probe {
            pick 1
            drop 0
            add
        }
    "#,
        ANNIHILATE,
    );
    assert_eq!(shape(&body), vec!["add"]);
}

#[test]
fn a_type_test_leaves_the_drop_behind() {
    // `is_int` consumes a value to make the one being dropped, so the drop
    // still has to happen — it just takes the input instead.
    let body = tree(
        r#"
        sentence probe {
            is_int
            drop 0
        }
    "#,
        ANNIHILATE,
    );
    assert_eq!(shape(&body), vec!["drop"]);
}

#[test]
fn a_partial_instruction_is_not_annihilated() {
    // `add; drop` is not `drop; drop`: the add still rejects non-numeric
    // operands, and cancelling it would discard that check.
    let body = tree(
        r#"
        sentence probe {
            add
            drop 0
        }
    "#,
        ANNIHILATE,
    );
    assert_eq!(shape(&body), vec!["add", "drop"]);
}

#[test]
fn passes_compose() {
    // Annihilating the push/drop pair leaves `push 7` shared by both arms,
    // which factoring then hoists — neither pass alone gets there.
    let code = r#"
        sentence probe {
            branch { push 7 push 9 drop 0 push 1 } { push 7 push 2 }
        }
    "#;
    assert_eq!(shape(&tree(code, FACTOR)), vec!["dip 1 { push 7 }", "branch"]);

    let both = tree(
        code,
        Passes {
            factor_branches: true,
            annihilate: true,
            dip_normalize: false,
        },
    );
    let Node::Branch { then_body, .. } = &both[1] else {
        panic!("expected a branch")
    };
    assert_eq!(shape(&both), vec!["dip 1 { push 7 }", "branch"]);
    assert_eq!(shape(then_body), vec!["push 1"]);
}

/// The rewrites must not change what a sentence does. Arity is the part of
/// that this tool can check for itself, and running it over every sentence
/// in the real corpus exercises far more instruction sequences than the
/// hand-written cases above.
///
/// Two different invariants are at play:
///
/// - Net change is preserved by every pass, exactly.
/// - The *input requirement* is preserved by the dip passes and by
///   factoring, but `--annihilate` may lower it: dropping `pick 2; drop`
///   also drops the demand for three values that only the `pick` made. The
///   rewritten code is defined on strictly more stacks than the original,
///   which is sound — so the bound is one-directional, not an equality.
#[test]
fn rewrites_preserve_arity_across_the_corpus() {
    // Tests run with the package root as the working directory.
    let main = Path::new("../tests/main.hana");
    let code = match fs::read_to_string(main) {
        Ok(code) => code,
        // Not a failure: the crate should still be testable on its own.
        Err(_) => return,
    };
    let library = bytecode::assemble_with_path(&code, main.parent()).unwrap();

    let mut checked = 0;
    for (s_idx, _) in library.names.iter_enumerated() {
        let plain = build(&library, s_idx, &mut HashSet::new());
        let name = || format!("#{} {}", usize::from(s_idx), library.names[s_idx]);

        // The dip passes and factoring preserve arity outright.
        for passes in [DIPS, FACTOR] {
            let mut rewritten = plain.clone();
            rewrite(&mut rewritten, passes);
            assert_eq!(
                seq_arity(&plain),
                seq_arity(&rewritten),
                "{:?} changed the arity of {}",
                passes,
                name()
            );
        }

        // Everything together preserves net change, and never asks for
        // more inputs than the original did.
        let mut all = plain.clone();
        rewrite(&mut all, ALL);
        assert_eq!(net(&plain), net(&all), "net change changed for {}", name());
        assert!(
            seq_arity(&all).0 <= seq_arity(&plain).0,
            "rewriting raised the input requirement of {}",
            name()
        );

        // Running to a fixpoint has to mean something: a second pass must find
        // nothing left to do. The flags guaranteed this by construction; now
        // that the search is separable from the rules it is worth asserting,
        // since a non-confluent rule set would show up here first.
        let mut twice = all.clone();
        assert!(
            !rewrite(&mut twice, ALL),
            "rewriting {} was not idempotent",
            name()
        );
        assert_eq!(all, twice, "rewriting {} was not idempotent", name());

        let mut unary = all.clone();
        expand_to_unary_dips(&mut unary);
        assert_eq!(
            seq_arity(&all),
            seq_arity(&unary),
            "unary expansion changed the arity of {}",
            name()
        );
        assert!(
            unary_only(&unary),
            "{} kept a dip deeper than 1 after expansion",
            name()
        );
        checked += 1;
    }

    assert!(checked > 500, "expected the full corpus, saw {}", checked);
}

/// Whether every dip in the tree hides at most one value.
fn unary_only(nodes: &[Node]) -> bool {
    nodes.iter().all(|node| match node {
        Node::Dip { depth, body, .. } => *depth <= 1 && unary_only(body),
        Node::Branch {
            then_body,
            else_body,
            ..
        } => unary_only(then_body) && unary_only(else_body),
        Node::Op(_) | Node::Cut(_) => true,
    })
}

#[test]
fn normalization_preserves_arity() {
    // The rewrite is supposed to be meaning-preserving; arity is the part
    // of the meaning this tool can check for itself.
    let code = r#"
        sentence probe {
            push 1
            dip 2 { add }
            roll 1
            dip 1 { drop 0 }
            add
        }
    "#;
    let plain = tree(code, Passes::default());
    let normalized = tree(code, DIPS);
    assert_ne!(shape(&plain), shape(&normalized), "expected some rewriting");
    assert_eq!(seq_arity(&plain), seq_arity(&normalized));
}

