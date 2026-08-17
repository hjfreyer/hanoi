//! The `.hant` file: proofs, written as strategies.
//!
//! An identity states a claim; the `.hant` beside the `.hana` says how to
//! discharge it. An identity with no entry gets the default — `egraph`, the
//! saturation engine alone — so the file holds exactly the proofs that need
//! a human's direction and nothing else:
//!
//! ```text
//! // identities.hant
//! proof identities::testing_a_test_by_name = inline egraph;
//! proof identities::something_harder =
//!     peel
//!     via { drop 0 push true } (left: inline egraph);
//! ```
//!
//! A strategy is a run of steps, juxtaposed, acting on **one goal**. The
//! manipulations transform it; a splitter replaces it with independent
//! subgoals, each carrying its own strategy; `egraph` closes it:
//!
//! | step | does | fails when |
//! |---|---|---|
//! | `peel` | strips what the two compose spines share at either end | nothing is shared |
//! | `inline` | unfolds every call, all the way down | there are no calls |
//! | `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B` | the waypoint's net stack change is not the goal's, or a side fails |
//! | `egraph` | saturates; the sides meet or the gas runs out | it runs out of gas |
//! | `descend(then: s, else: s)` | forks a branch-vs-branch goal into its arms | the sides are not branches, or an omitted arm is not already equal |
//!
//! `egraph`, `via` and `descend` end a strategy — the goal is closed or
//! split, and what follows a split is written *inside* it, since the
//! subgoals are independent: peel one, inline the other, cut one again.
//! A chain is nested cuts — `via { c1 } (right: via { c2 })` — and each
//! link may take a different road. A strategy that ends on a manipulation
//! is allowed: it closes only if the goal has become trivially equal, and
//! says so otherwise.
//!
//! The two splitters treat an omitted side differently, on purpose. An
//! omitted `descend` arm is a *checked claim* that those arms are already
//! equal — the goal supplied the arms, and equal ones are common. A cut's
//! sides are the author's construction, and a cut with a trivially equal
//! side is a degenerate cut; an omitted `via` side gets `egraph`, because
//! handing the engine easier halves is what a cut is *for*.
//!
//! Entries are checked both ways: an entry naming no stated identity is an
//! error (a renamed identity must not silently shed its proof), and a claim
//! discharged twice was discharged once too often.
//!
//! `via` bodies are programs, compiled by appending scratch sentences to the
//! corpus source so the real parser and resolver do the work — with the one
//! caveat that paths in a body resolve from the crate root.

use std::fmt;

/// One step of a strategy. `V` is what a `via` carries: the body's source
/// text as parsed, a lowered [`Term`](crate::term::Term) once the corpus it
/// compiles against exists.
#[derive(Debug, Clone, PartialEq)]
pub enum Step<V> {
    /// Saturate. Closes the goal or fails with a residual.
    Egraph,
    /// Strip the shared affixes of the two compose spines.
    Peel,
    /// Unfold every call on both sides.
    Inline,
    /// Cut the goal at a waypoint: `A = B` splits into the two independent
    /// goals `A = C` (left) and `C = B` (right), each discharged by its own
    /// strategy. An omitted side gets the default, `egraph` — a cut exists
    /// to hand the engine easier halves, so the engine is what an unnamed
    /// half gets.
    Via {
        waypoint: V,
        left: Option<Strategy<V>>,
        right: Option<Strategy<V>>,
    },
    /// Fork a branch-vs-branch goal into its arms. An omitted arm claims
    /// those arms are already equal, and the claim is checked.
    Descend {
        then_arm: Option<Strategy<V>>,
        else_arm: Option<Strategy<V>>,
    },
}

/// A strategy: steps in order, manipulations first, at most one closer last.
pub type Strategy<V> = Vec<Step<V>>;

/// A parsed `.hant` entry: which identity, and how to prove it.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofEntry {
    pub identity: String,
    pub strategy: Strategy<String>,
}

/// The default for an identity with no entry: the engine alone.
pub fn default_strategy<V>() -> Strategy<V> {
    vec![Step::Egraph]
}

/// Maps every `via` body through `f` — how a parsed strategy becomes a
/// runnable one once the corpus its bodies compile against exists.
pub fn map_via<V, W, E>(
    strategy: Strategy<V>,
    f: &mut impl FnMut(V) -> Result<W, E>,
) -> Result<Strategy<W>, E> {
    strategy
        .into_iter()
        .map(|step| {
            Ok(match step {
                Step::Egraph => Step::Egraph,
                Step::Peel => Step::Peel,
                Step::Inline => Step::Inline,
                Step::Via {
                    waypoint,
                    left,
                    right,
                } => Step::Via {
                    waypoint: f(waypoint)?,
                    left: left.map(|s| map_via(s, f)).transpose()?,
                    right: right.map(|s| map_via(s, f)).transpose()?,
                },
                Step::Descend { then_arm, else_arm } => Step::Descend {
                    then_arm: then_arm.map(|s| map_via(s, f)).transpose()?,
                    else_arm: else_arm.map(|s| map_via(s, f)).transpose()?,
                },
            })
        })
        .collect()
}

/// Every `via` body in a strategy, in reading order — the collection pass
/// that decides what scratch sentences the corpus needs.
pub fn via_bodies<V: Clone>(strategy: &Strategy<V>) -> Vec<V> {
    let mut out = Vec::new();
    for step in strategy {
        match step {
            Step::Via {
                waypoint,
                left,
                right,
            } => {
                out.push(waypoint.clone());
                for side in [left, right].into_iter().flatten() {
                    out.extend(via_bodies(side));
                }
            }
            Step::Descend { then_arm, else_arm } => {
                for arm in [then_arm, else_arm].into_iter().flatten() {
                    out.extend(via_bodies(arm));
                }
            }
            _ => {}
        }
    }
    out
}

impl<V> fmt::Display for Step<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Step::Egraph => write!(f, "egraph"),
            Step::Peel => write!(f, "peel"),
            Step::Inline => write!(f, "inline"),
            Step::Via { .. } => write!(f, "via {{ … }}"),
            Step::Descend { .. } => write!(f, "descend(…)"),
        }
    }
}

// ---- parsing ----------------------------------------------------------------

/// Parses a `.hant` file's text into its entries.
pub fn parse_hant(text: &str) -> Result<Vec<ProofEntry>, String> {
    let text = strip_comments(text);
    let mut rest = text.trim_start();
    let mut entries = Vec::new();
    while !rest.is_empty() {
        let after_kw = rest
            .strip_prefix("proof")
            .filter(|r| r.starts_with(char::is_whitespace))
            .ok_or_else(|| format!("expected `proof`, found: {}", head_of(rest)))?
            .trim_start();
        let name_len = after_kw
            .find(|c: char| c.is_whitespace() || c == '=')
            .ok_or("a proof ends before naming an identity")?;
        let (identity, after_name) = after_kw.split_at(name_len);
        let after_eq = after_name
            .trim_start()
            .strip_prefix('=')
            .ok_or_else(|| format!("proof {}: expected `=`", identity))?;
        let (strategy, after_strategy) =
            parse_strategy(after_eq).map_err(|e| format!("proof {}: {}", identity, e))?;
        rest = after_strategy
            .trim_start()
            .strip_prefix(';')
            .ok_or_else(|| format!("proof {}: expected `;` after the strategy", identity))?
            .trim_start();
        validate(&strategy).map_err(|e| format!("proof {}: {}", identity, e))?;
        entries.push(ProofEntry {
            identity: identity.to_string(),
            strategy,
        });
    }
    Ok(entries)
}

/// Steps by juxtaposition, ending at `;`, `,` or `)` — whichever encloses.
fn parse_strategy(input: &str) -> Result<(Strategy<String>, &str), String> {
    let mut rest = input.trim_start();
    let mut steps = Vec::new();
    while !rest.is_empty() && !rest.starts_with([';', ',', ')']) {
        let (step, after) = parse_step(rest)?;
        steps.push(step);
        rest = after.trim_start();
    }
    if steps.is_empty() {
        return Err("an empty strategy proves nothing".to_string());
    }
    Ok((steps, rest))
}

fn parse_step(input: &str) -> Result<(Step<String>, &str), String> {
    let word_len = input
        .find(|c: char| !(c.is_alphanumeric() || c == '_'))
        .unwrap_or(input.len());
    let (word, rest) = input.split_at(word_len);
    match word {
        "egraph" => Ok((Step::Egraph, rest)),
        "peel" => Ok((Step::Peel, rest)),
        "inline" => Ok((Step::Inline, rest)),
        "via" => {
            let (body, after) =
                brace_block(rest.trim_start()).ok_or("`via` expects a braced body")?;
            let (sides, after) = if after.trim_start().starts_with('(') {
                let (arms, rest) = parse_arms("via", "left", "right", after.trim_start())?;
                (arms, rest)
            } else {
                ((None, None), after)
            };
            Ok((
                Step::Via {
                    waypoint: body.trim().to_string(),
                    left: sides.0,
                    right: sides.1,
                },
                after,
            ))
        }
        "descend" => {
            let rest = rest.trim_start();
            if !rest.starts_with('(') {
                return Err("`descend` expects `(then: …, else: …)`".to_string());
            }
            let ((then_arm, else_arm), after) = parse_arms("descend", "then", "else", rest)?;
            Ok((Step::Descend { then_arm, else_arm }, after))
        }
        "" => Err(format!("expected a step, found: {}", head_of(input))),
        other => Err(format!("no step is called `{}`", other)),
    }
}

/// Two arms in parentheses, either labelled and either omissible:
/// `(then: s, else: s)` for `descend`, `(left: s, right: s)` for `via`.
#[allow(clippy::type_complexity)]
fn parse_arms<'t>(
    step: &str,
    first: &str,
    second: &str,
    input: &'t str,
) -> Result<
    (
        (Option<Strategy<String>>, Option<Strategy<String>>),
        &'t str,
    ),
    String,
> {
    let mut rest = input
        .strip_prefix('(')
        .expect("the caller saw the open paren");
    let mut first_arm = None;
    let mut second_arm = None;
    loop {
        rest = rest.trim_start();
        if let Some(after) = rest.strip_prefix(')') {
            return Ok(((first_arm, second_arm), after));
        }
        let (label, slot) = if let Some(r) = rest.strip_prefix(&format!("{}:", first)) {
            (r, &mut first_arm)
        } else if let Some(r) = rest.strip_prefix(&format!("{}:", second)) {
            (r, &mut second_arm)
        } else {
            return Err(format!(
                "`{}` sides are `{}:` or `{}:`, found: {}",
                step,
                first,
                second,
                head_of(rest)
            ));
        };
        if slot.is_some() {
            return Err(format!("`{}` names a side twice", step));
        }
        let (strategy, after) = parse_strategy(label)?;
        *slot = Some(strategy);
        rest = after.trim_start().strip_prefix(',').unwrap_or(after);
    }
}

/// The closers close: nothing may follow `egraph`, `via` or `descend` — a
/// split goal's remaining work is written inside the split, since the
/// subgoals are independent. Sides and arms answer for themselves.
fn validate<V>(strategy: &Strategy<V>) -> Result<(), String> {
    for (i, step) in strategy.iter().enumerate() {
        let last = i + 1 == strategy.len();
        match step {
            Step::Egraph | Step::Descend { .. } | Step::Via { .. } if !last => {
                return Err(format!("`{}` closes the goal; nothing can follow it", step));
            }
            Step::Descend { then_arm, else_arm } => {
                for arm in [then_arm, else_arm].into_iter().flatten() {
                    validate(arm)?;
                }
            }
            Step::Via { left, right, .. } => {
                for side in [left, right].into_iter().flatten() {
                    validate(side)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn strip_comments(text: &str) -> String {
    text.lines()
        .map(|line| line.split_once("//").map_or(line, |(code, _)| code))
        .collect::<Vec<_>>()
        .join("\n")
}

fn head_of(rest: &str) -> String {
    rest.chars().take(24).collect()
}

/// Splits `{ ... }` off the front, brace-balanced, answering the inside and
/// what follows the closing brace.
fn brace_block(text: &str) -> Option<(&str, &str)> {
    let mut chars = text.char_indices();
    let (_, '{') = chars.next()? else { return None };
    let mut depth = 1usize;
    for (i, c) in chars {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some((&text[1..i], &text[i + 1..]));
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_proof_file_parses_into_its_entries() {
        let entries = parse_hant(
            r#"
            // how the hard ones close
            proof identities::by_name = inline egraph;
            proof identities::wrapped =
                descend(then: peel via { drop 0 push true }, else: egraph);
            "#,
        )
        .unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].identity, "identities::by_name");
        assert_eq!(entries[0].strategy, vec![Step::Inline, Step::Egraph]);
        let [Step::Descend { then_arm, else_arm }] = &entries[1].strategy[..] else {
            panic!("{:?}", entries[1].strategy);
        };
        assert_eq!(
            then_arm.as_deref(),
            Some(
                [
                    Step::Peel,
                    Step::Via {
                        waypoint: "drop 0 push true".to_string(),
                        left: None,
                        right: None,
                    },
                ]
                .as_slice()
            )
        );
        assert_eq!(else_arm.as_deref(), Some([Step::Egraph].as_slice()));
    }

    #[test]
    fn an_omitted_descend_arm_stays_omitted() {
        let entries = parse_hant("proof p = descend(then: egraph);").unwrap();
        let [Step::Descend { then_arm, else_arm }] = &entries[0].strategy[..] else {
            panic!();
        };
        assert!(then_arm.is_some());
        assert!(else_arm.is_none());
    }

    #[test]
    fn a_closer_mid_strategy_is_refused() {
        let err = parse_hant("proof p = egraph inline;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        let err = parse_hant("proof p = descend(then: egraph peel);").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
    }

    #[test]
    fn a_malformed_entry_is_refused_with_its_name() {
        let err = parse_hant("proof foo = flatten;").unwrap_err();
        assert!(err.contains("foo") && err.contains("flatten"), "{}", err);
        let err = parse_hant("proof foo = ;").unwrap_err();
        assert!(err.contains("empty strategy"), "{}", err);
        let err = parse_hant("prove foo = egraph;").unwrap_err();
        assert!(err.contains("expected `proof`"), "{}", err);
    }

    #[test]
    fn via_bodies_are_collected_in_reading_order() {
        let entries = parse_hant(
            "proof p = descend(then: via { push 1 } (left: via { push 2 }), else: via { push 3 });",
        )
        .unwrap();
        assert_eq!(
            via_bodies(&entries[0].strategy),
            vec![
                "push 1".to_string(),
                "push 2".to_string(),
                "push 3".to_string()
            ]
        );
    }

    #[test]
    fn a_cut_closes_its_goal() {
        // Nothing follows a split: the subgoals' work is written inside it.
        let err = parse_hant("proof p = via { push 1 } egraph;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        // A chain is nested cuts, and each side may take its own road.
        let entries =
            parse_hant("proof p = via { push 1 } (left: peel egraph, right: via { push 2 });")
                .unwrap();
        let [Step::Via { left, right, .. }] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(left.as_deref(), Some([Step::Peel, Step::Egraph].as_slice()));
        assert!(matches!(right.as_deref(), Some([Step::Via { .. }])));
    }
}
