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
//!     via { drop(1) ; push true } (left: inline egraph);
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
//! | `inline(name)` | unfolds the calls to that one sentence | it is not called here |
//! | `symm` | swaps the two sides | never — but two in a row are refused |
//! | `exact` | closes the goal if the sides are one term as written | they differ — and the residual is the goal untouched, which is what the step is usually for |
//! | `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B` | the waypoint's net stack change is not the goal's, or a side fails |
//! | `solve (f: 1 -> 1) { … ?f … } (right: s)` | **cuts at a waypoint the engine fills in**: match the template against the left side, continue with `C[fills] = B` | the template's net is not the goal's, no match binds the variables at their declared arities, or the right half fails |
//! | `egraph` | saturates; the sides meet or the gas runs out | it runs out of gas |
//! | `descend(then: s, else: s)` | forks a branch-vs-branch goal into its arms | the sides are not branches, or an omitted arm is not already equal |
//! | `norm (left: s, right: s)` | **cuts at the left side's normal form**: `A = B` splits into `A = NF(A)` and `NF(A) = B`, with the case tree reified as the waypoint | a half fails |
//! | `norm_trusted (right: s)` | the same cut with `A = NF(A)` closed on the normalizer's word | the right half fails |
//!
//! `egraph`, `via` and `descend` end a strategy — the goal is closed or
//! split, and what follows a split is written *inside* it, since the
//! subgoals are independent: peel one, inline the other, cut one again.
//! A chain is nested cuts — `via { c1 } (right: via { c2 })` — and each
//! link may take a different road. A strategy that ends on a manipulation
//! is allowed: it closes only if the goal has become trivially equal, and
//! says so otherwise.
//!
//! `symm` is the one step that changes nothing about the claim: equality is
//! symmetric, so `A = B` and `B = A` are the same goal. What it changes is
//! which side the *asymmetric* steps read — `solve` matches its template
//! against the left side, and a `via`'s halves are named for their sides —
//! so it is how a proof says "the interesting side is the other one" without
//! restating the identity backwards.
//!
//! `solve` is `via` with the waypoint under-specified: `?vars` stand for
//! unknown subprograms at declared arities, and *solving* means saturating
//! the goal and matching the template against the left side's class — which
//! finds the fills and proves `A = C[fills]` in one motion, since a match
//! is an instantiation living in that very class. The first match at the
//! declared arities wins, and the fills are recorded in the proof so a
//! different match after a rule-set change is visible rather than
//! mysterious. Only the right half remains as a goal.
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
//! A body — a `via` waypoint or a `solve` template — is a **term**, in the
//! language [`crate::term`] prints and [`crate::parse`] reads: the same
//! language a residual is reported in, so answering a stuck goal is copying
//! and editing rather than translating. `call name` names a sentence, `?f` a
//! declared variable, and nothing pads — `id(k) * A` is written where a Hana
//! sentence would have inferred it.

use std::fmt;

use bytecode::SentenceIndex;

use crate::term::Term;

/// One step of a strategy. `V` is what a `via` carries: the body's text as
/// parsed, a [`Body`] — the term it reads as — once the library it is written
/// against exists.
#[derive(Debug, Clone, PartialEq)]
pub enum Step<V> {
    /// Saturate. Closes the goal or fails with a residual.
    Egraph,
    /// Strip the shared affixes of the two compose spines.
    Peel,
    /// Unfold calls on both sides: every one, all the way down, or — with a
    /// label — only the calls to the sentence it names, whose own calls stay
    /// closed. Recursion is forbidden, so one pass opens every instance.
    Inline(Option<V>),
    /// Swap the two sides. Equality is symmetric, so the claim is untouched;
    /// what moves is which side the asymmetric steps read.
    Symm,
    /// Close the goal only if the two sides are one term as written. No
    /// search runs, so a failed `exact` reports the goal exactly as it
    /// stands — un-saturated, un-narrowed — which is the way to *see* a
    /// goal: `exact` alone shows the identity as lowered and aligned, and
    /// after a manipulation it shows what the manipulation left.
    Exact,
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
    /// Cut the goal at a waypoint the engine fills in. The template's
    /// `?vars` stand for unknown subprograms at declared arities; solving
    /// means matching the template against the left side's saturated class,
    /// which both finds the fills and proves `A = C[fills]` in one motion.
    /// The goal continues as `C[fills] = B` under `right`.
    Solve {
        vars: SolveVars,
        template: V,
        right: Option<Strategy<V>>,
    },
    /// Fork a branch-vs-branch goal into its arms. An omitted arm claims
    /// those arms are already equal, and the claim is checked.
    Descend {
        then_arm: Option<Strategy<V>>,
        else_arm: Option<Strategy<V>>,
    },
    /// Cut the goal at a waypoint the normalizer computes: the **left**
    /// side's case-tree normal form ([`crate::nf`]), reified back into a
    /// term. `A = B` splits into `A = NF(A)` and `NF(A) = B`, each half
    /// closed by its own strategy, `egraph` by default. One side only, so
    /// the step composes: a right half that needs normalizing too writes
    /// `symm norm…` inside itself, and when both sides normalize to one
    /// tree the chain's last goal is one term as written. With `trusted`
    /// the left half closes on the normalizer's word instead of carrying a
    /// strategy — the trade of trusted surface for not depending on the
    /// rule set reaching the reified spelling.
    Norm {
        trusted: bool,
        left: Option<Strategy<V>>,
        right: Option<Strategy<V>>,
    },
}

/// What a step's payload reads as, once the library it names things against
/// exists: a term, a term with holes, or a sentence.
#[derive(Debug, Clone, PartialEq)]
pub enum Body {
    /// A `via` waypoint: the lowered term itself.
    Stone(Term),
    /// A `solve` template: the term, with each declared variable standing as
    /// a leaf of the declared arity — a call to an index no sentence has.
    Template {
        term: Term,
        /// Parallel to the step's `vars`: which leaf each `?var` is.
        holes: Vec<(String, SentenceIndex)>,
    },
    /// An `inline` label: the one sentence it opens.
    Target(SentenceIndex),
}

/// A strategy: steps in order, manipulations first, at most one closer last.
pub type Strategy<V> = Vec<Step<V>>;

/// The variables a `solve` declares: name and arity, `(inputs, outputs)`.
pub type SolveVars = Vec<(String, (usize, usize))>;

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

impl<V> fmt::Display for Step<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Step::Egraph => write!(f, "egraph"),
            Step::Peel => write!(f, "peel"),
            Step::Inline(None) => write!(f, "inline"),
            Step::Inline(Some(_)) => write!(f, "inline(…)"),
            Step::Symm => write!(f, "symm"),
            Step::Exact => write!(f, "exact"),
            Step::Via { .. } => write!(f, "via {{ … }}"),
            Step::Solve { .. } => write!(f, "solve(…)"),
            Step::Descend { .. } => write!(f, "descend(…)"),
            Step::Norm { trusted: false, .. } => write!(f, "norm"),
            Step::Norm { trusted: true, .. } => write!(f, "norm_trusted"),
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
        "inline" => {
            // A label goes in parentheses, so `inline egraph` stays two steps
            // rather than an inline of a sentence called `egraph`.
            let Some(after) = rest.trim_start().strip_prefix('(') else {
                return Ok((Step::Inline(None), rest));
            };
            let (label, after) = after.split_once(')').ok_or("`inline(` never closes")?;
            let label = label.trim();
            if label.is_empty() {
                return Err("`inline()` names no sentence".to_string());
            }
            Ok((Step::Inline(Some(label.to_string())), after))
        }
        "symm" => Ok((Step::Symm, rest)),
        "exact" => Ok((Step::Exact, rest)),
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
        "solve" => {
            let rest = rest.trim_start();
            if !rest.starts_with('(') {
                return Err(
                    "`solve` expects its variables first: `solve (f: 1 -> 1) { … ?f … }`"
                        .to_string(),
                );
            }
            let (vars, after) = parse_solve_vars(rest)?;
            if vars.is_empty() {
                return Err("`solve` with no variables is `via`".to_string());
            }
            let (body, after) =
                brace_block(after.trim_start()).ok_or("`solve` expects a braced template")?;
            let (right, after) = if after.trim_start().starts_with('(') {
                let ((right, none), rest) =
                    parse_arms("solve", "right", "right", after.trim_start())?;
                debug_assert!(none.is_none());
                (right, rest)
            } else {
                (None, after)
            };
            Ok((
                Step::Solve {
                    vars,
                    template: body.trim().to_string(),
                    right,
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
        "norm" => {
            // The halves take strategies like a `via`'s, and for the same
            // reason: the normal form is a waypoint, just a computed one.
            let (sides, after) = if rest.trim_start().starts_with('(') {
                parse_arms("norm", "left", "right", rest.trim_start())?
            } else {
                ((None, None), rest)
            };
            Ok((
                Step::Norm {
                    trusted: false,
                    left: sides.0,
                    right: sides.1,
                },
                after,
            ))
        }
        "norm_trusted" => {
            // Only a right side: the left half is the one the trust closes,
            // so a strategy for it would direct nothing.
            let (right, after) = if rest.trim_start().starts_with('(') {
                let ((right, none), rest) =
                    parse_arms("norm_trusted", "right", "right", rest.trim_start())?;
                debug_assert!(none.is_none());
                (right, rest)
            } else {
                (None, rest)
            };
            Ok((
                Step::Norm {
                    trusted: true,
                    left: None,
                    right,
                },
                after,
            ))
        }
        "" => Err(format!("expected a step, found: {}", head_of(input))),
        other => Err(format!("no step is called `{}`", other)),
    }
}

/// `(f: 1 -> 1, g: 2 -> 1)` — the variables a `solve` template binds.
fn parse_solve_vars(input: &str) -> Result<(SolveVars, &str), String> {
    let mut rest = input
        .strip_prefix('(')
        .expect("the caller saw the open paren");
    let mut vars = Vec::new();
    loop {
        rest = rest.trim_start();
        if let Some(after) = rest.strip_prefix(')') {
            return Ok((vars, after));
        }
        let name_len = rest
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let (name, after_name) = rest.split_at(name_len);
        if name.is_empty() {
            return Err(format!(
                "`solve` expects `name: inputs -> outputs`, found: {}",
                head_of(rest)
            ));
        }
        let after_colon = after_name
            .trim_start()
            .strip_prefix(':')
            .ok_or_else(|| format!("variable {}: expected `:` and an arity", name))?;
        let (inputs, after_inputs) = parse_number(after_colon.trim_start())
            .ok_or_else(|| format!("variable {}: expected an input count", name))?;
        let after_arrow = after_inputs
            .trim_start()
            .strip_prefix("->")
            .ok_or_else(|| format!("variable {}: expected `->`", name))?;
        let (outputs, after_outputs) = parse_number(after_arrow.trim_start())
            .ok_or_else(|| format!("variable {}: expected an output count", name))?;
        if vars.iter().any(|(n, _)| n == name) {
            return Err(format!("`solve` declares {} twice", name));
        }
        vars.push((name.to_string(), (inputs, outputs)));
        rest = after_outputs.trim_start();
        rest = rest.strip_prefix(',').unwrap_or(rest);
    }
}

fn parse_number(input: &str) -> Option<(usize, &str)> {
    let len = input
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(input.len());
    (len > 0).then(|| (input[..len].parse().expect("digits parse"), &input[len..]))
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
            Step::Egraph
            | Step::Exact
            | Step::Descend { .. }
            | Step::Via { .. }
            | Step::Solve { .. }
            | Step::Norm { .. }
                if !last =>
            {
                return Err(format!("`{}` closes the goal; nothing can follow it", step));
            }
            Step::Descend { then_arm, else_arm } => {
                for arm in [then_arm, else_arm].into_iter().flatten() {
                    validate(arm)?;
                }
            }
            Step::Via { left, right, .. } | Step::Norm { left, right, .. } => {
                for side in [left, right].into_iter().flatten() {
                    validate(side)?;
                }
            }
            Step::Solve { right, .. } => {
                for side in right.iter() {
                    validate(side)?;
                }
            }
            // Swapping twice is the goal it started with, and a step that
            // says nothing is a step whose author lost the thread.
            Step::Symm if matches!(strategy.get(i + 1), Some(Step::Symm)) => {
                return Err("`symm symm` is the goal unchanged".to_string());
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
                descend(then: peel via { drop(1) ; push true }, else: egraph);
            "#,
        )
        .unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].identity, "identities::by_name");
        assert_eq!(entries[0].strategy, vec![Step::Inline(None), Step::Egraph]);
        let [Step::Descend { then_arm, else_arm }] = &entries[1].strategy[..] else {
            panic!("{:?}", entries[1].strategy);
        };
        assert_eq!(
            then_arm.as_deref(),
            Some(
                [
                    Step::Peel,
                    Step::Via {
                        waypoint: "drop(1) ; push true".to_string(),
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

    #[test]
    fn solve_parses_vars_template_and_right() {
        let entries =
            parse_hant("proof p = solve (f: 1 -> 0, g: 2 -> 1) { ?f ; ?g } (right: egraph);")
                .unwrap();
        let [
            Step::Solve {
                vars,
                template,
                right,
            },
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(
            vars,
            &[("f".to_string(), (1, 0)), ("g".to_string(), (2, 1))]
        );
        assert_eq!(template, "?f ; ?g");
        assert_eq!(right.as_deref(), Some([Step::Egraph].as_slice()));
    }

    #[test]
    fn an_inline_label_is_parenthesized() {
        // Parenthesized so that `inline egraph` stays two steps.
        let entries = parse_hant("proof p = inline egraph;").unwrap();
        assert_eq!(entries[0].strategy, vec![Step::Inline(None), Step::Egraph]);
        let entries = parse_hant("proof p = inline(types_test::is_tag) egraph;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![
                Step::Inline(Some("types_test::is_tag".to_string())),
                Step::Egraph
            ]
        );
        let err = parse_hant("proof p = inline() egraph;").unwrap_err();
        assert!(err.contains("names no sentence"), "{}", err);
    }

    #[test]
    fn exact_is_a_closer() {
        let entries = parse_hant("proof p = inline exact;").unwrap();
        assert_eq!(entries[0].strategy, vec![Step::Inline(None), Step::Exact]);
        let err = parse_hant("proof p = exact egraph;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
    }

    #[test]
    fn symm_parses_and_says_nothing_twice() {
        let entries = parse_hant("proof p = symm peel egraph;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![Step::Symm, Step::Peel, Step::Egraph]
        );
        let err = parse_hant("proof p = symm symm egraph;").unwrap_err();
        assert!(err.contains("`symm symm`"), "{}", err);
    }

    #[test]
    fn norm_parses_bare_with_sides_and_trusted() {
        let entries = parse_hant("proof p = norm;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![Step::Norm {
                trusted: false,
                left: None,
                right: None,
            }]
        );
        let entries = parse_hant("proof p = norm (left: peel egraph, right: inline);").unwrap();
        let [
            Step::Norm {
                trusted: false,
                left,
                right,
            },
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(left.as_deref(), Some([Step::Peel, Step::Egraph].as_slice()));
        assert_eq!(right.as_deref(), Some([Step::Inline(None)].as_slice()));
        let entries = parse_hant("proof p = inline norm_trusted;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![
                Step::Inline(None),
                Step::Norm {
                    trusted: true,
                    left: None,
                    right: None,
                }
            ]
        );
        // The trusted spelling takes a right side — and only a right side,
        // since the left half is the one the trust closes.
        let entries = parse_hant("proof p = norm_trusted (right: symm norm_trusted);").unwrap();
        let [
            Step::Norm {
                trusted: true,
                left: None,
                right: Some(right),
            },
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        assert!(matches!(
            right[..],
            [Step::Symm, Step::Norm { trusted: true, .. }]
        ));
        let err = parse_hant("proof p = norm_trusted (left: egraph);").unwrap_err();
        assert!(err.contains("`right:`"), "{}", err);
    }

    #[test]
    fn norm_is_a_closer() {
        let err = parse_hant("proof p = norm egraph;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        let err = parse_hant("proof p = norm_trusted egraph;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
    }

    #[test]
    fn solve_is_a_closer_with_checked_variables() {
        let err = parse_hant("proof p = solve (f: 1 -> 1) { ?f } egraph;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        let err = parse_hant("proof p = solve () { x };").unwrap_err();
        assert!(err.contains("no variables"), "{}", err);
        let err = parse_hant("proof p = solve (f: 1 -> 1, f: 2 -> 2) { ?f };").unwrap_err();
        assert!(err.contains("twice"), "{}", err);
    }
}
