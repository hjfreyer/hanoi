//! Tactics: the search, separated from the rules it drives.
//!
//! A tactic is a partial function on a node sequence. It either matches and
//! changes something, matches and changes nothing, or fails — and a tactic
//! that fails hands the sequence back exactly as it received it, which is what
//! makes rollback a matter of ownership rather than of copying.
//!
//! The governing invariant: **a tactic's result depends only on the sequence
//! it is given, never on where in the tree it is being applied.** Anything that
//! would need to know its position (a traversal-local visited set, say) belongs
//! in [`Env`] as a fact about the whole library instead.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};

use crate::arity::seq_arity;
use crate::ir::{child_bodies, selected_bodies, Node, Selector};
use crate::program::Program;
use crate::rules::Rule;

/// How many rule firings the trace remembers. Enough to read an oscillation
/// off the end of it, not enough to bury the error message.
const TRACE_WINDOW: usize = 24;

/// What applying a tactic did.
///
/// `Failed` carries the sequence back out untouched. That is a contract, not a
/// convention: `Seq` and `Choice` rely on it to avoid cloning.
///
/// Note what *does not* fail: a rule that matches nowhere reports `Unchanged`.
/// Scanning a sequence and finding no work is a successful no-op, not an
/// error, and treating it as one made `a; b` throw away everything `a` did
/// whenever `b` had nothing to do — silently, while the trace still reported
/// `a` firing. `Failed` comes only from an explicit `fail` and from the aimed
/// combinators (`at`, `then_at`, `else_at`, `body_at`): a sweep that finds
/// nothing has looked everywhere and is done, but an aimed step that misses
/// points at the wrong place, and continuing would let every later step of a
/// script fire somewhere it was not aimed.
#[derive(Debug)]
pub(crate) enum Outcome {
    Changed(Vec<Node>),
    Unchanged(Vec<Node>),
    Failed(Vec<Node>),
}

impl Outcome {
    pub(crate) fn into_nodes(self) -> Vec<Node> {
        match self {
            Outcome::Changed(n) | Outcome::Unchanged(n) | Outcome::Failed(n) => n,
        }
    }

    fn changed(&self) -> bool {
        matches!(self, Outcome::Changed(_))
    }
}

#[derive(Debug)]
pub(crate) enum TacticError {
    /// The budget ran out. Almost always an oscillation between two rules that
    /// undo each other, which the recent-firings list makes obvious.
    OutOfFuel { spent: u64, recent: Vec<String> },
    /// `--check` caught a rule changing a window's net stack effect.
    NetChanged {
        rule: &'static str,
        before: Option<i64>,
        after: Option<i64>,
    },
}

impl std::fmt::Display for TacticError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TacticError::OutOfFuel { spent, recent } => {
                writeln!(f, "out of fuel after {} rule firings.", spent)?;
                writeln!(f)?;
                writeln!(f, "The last {} firings were:", recent.len())?;
                for r in recent {
                    writeln!(f, "  {}", r)?;
                }
                writeln!(f)?;
                write!(
                    f,
                    "A rule alternating with its inverse looks exactly like this. \
                     `collapse` and `expand` are inverses; so are any pair you write \
                     into one `repeat`. Raise the budget with --fuel if the work is \
                     genuinely this large."
                )
            }
            TacticError::NetChanged {
                rule,
                before,
                after,
            } => write!(
                f,
                "rule '{}' changed the net stack effect of the window it rewrote \
                 ({:?} -> {:?}). Learning an arity that was previously unknown is \
                 allowed; changing or losing one is a bug in the rule, not in the \
                 script.",
                rule, before, after
            ),
        }
    }
}

pub(crate) struct Env<'a> {
    prog: &'a Program<'a>,
    fuel: Cell<u64>,
    spent: Cell<u64>,
    recent: RefCell<VecDeque<String>>,
    hits: RefCell<HashMap<&'static str, usize>>,
    check: bool,
}

impl<'a> Env<'a> {
    pub(crate) fn new(prog: &'a Program<'a>, fuel: u64, check: bool) -> Self {
        Env {
            prog,
            fuel: Cell::new(fuel),
            spent: Cell::new(0),
            recent: RefCell::new(VecDeque::new()),
            hits: RefCell::new(HashMap::new()),
            check,
        }
    }

    /// Charged once per rule *firing*, globally across the run.
    ///
    /// Firings rather than attempts, because that is what bounds divergence:
    /// `each` terminates on its own and `repeat` only goes round again when
    /// something changed, so a loop that never ends must fire without end.
    /// Counting attempts instead would make the budget a measure of tree size
    /// rather than of work, and the number needed would depend on the input.
    fn spend(&self) -> Result<(), TacticError> {
        let left = self.fuel.get();
        self.spent.set(self.spent.get() + 1);
        if left == 0 {
            return Err(TacticError::OutOfFuel {
                spent: self.spent.get(),
                recent: self.recent.borrow().iter().cloned().collect(),
            });
        }
        self.fuel.set(left - 1);
        Ok(())
    }

    fn note(&self, rule: &'static str, at: usize) {
        *self.hits.borrow_mut().entry(rule).or_insert(0) += 1;
        let mut recent = self.recent.borrow_mut();
        if recent.len() == TRACE_WINDOW {
            recent.pop_front();
        }
        recent.push_back(format!("{}@{}", rule, at));
    }

    pub(crate) fn program(&self) -> &Program<'a> {
        self.prog
    }

    /// Rule firing counts, most frequent first.
    pub(crate) fn histogram(&self) -> Vec<(&'static str, usize)> {
        let mut out: Vec<_> = self.hits.borrow().iter().map(|(k, v)| (*k, *v)).collect();
        out.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        out
    }
}

#[derive(Debug)]
pub(crate) enum Tactic {
    /// Apply these rules at every position, left to right, to exhaustion.
    Each(Vec<&'static dyn Rule>),
    /// Apply the first rule that matches, at the first position it matches.
    Once(Vec<&'static dyn Rule>),
    /// Apply the first of these rules whose window matches anchored exactly
    /// at the given index — once, with no cascade rescan. A miss is `Failed`:
    /// an aimed step that does not fire was aimed at the wrong place.
    At(usize, Vec<&'static dyn Rule>),
    /// Apply to one child sequence of the node at the given index. `Failed`
    /// when that node has no child of the selected kind — where `then(t)`
    /// visits every branch in the sequence and skipping is the point, an
    /// aimed descent through the wrong node is a script error.
    IntoAt(Selector, usize, Box<Tactic>),
    Seq(Vec<Tactic>),
    Choice(Vec<Tactic>),
    Try(Box<Tactic>),
    Repeat(Box<Tactic>),
    RepeatN(usize, Box<Tactic>),
    /// Apply to every child sequence, one level down. Never fails.
    Children(Box<Tactic>),
    /// Apply to one *kind* of child sequence, one level down. Never fails.
    ///
    /// `children` is this with every selector at once. Splitting them out is
    /// what lets a script open one branch arm and leave the other alone —
    /// without it, staged inlining stops dead as soon as the remaining calls
    /// live inside arms, since `once` works on a single sequence and `children`
    /// cannot be aimed.
    Into(Selector, Box<Tactic>),
    /// Children first, then here. Never fails.
    Bu(Box<Tactic>),
    /// Here first, then children. Never fails.
    ///
    /// The direction matters most for `inline`, and not in the way you might
    /// guess. `td` expands a call and then immediately descends into the body
    /// it just created, so **one `td` pass expands the whole call graph**.
    /// `bu` reaches the newly created bodies only on the next pass, so
    /// `repeat_n(k, bu(each(inline)))` is what gives you k levels.
    Td(Box<Tactic>),
    Id,
    Fail,
}

/// Whether a tactic can report `Failed`.
///
/// Used to decide whether `Seq` and `Choice` need to save a copy for rollback.
/// Since only an explicit `fail` can fail, nothing built from rules ever
/// clones.
fn can_fail(t: &Tactic) -> bool {
    match t {
        Tactic::Fail | Tactic::At(..) | Tactic::IntoAt(..) => true,
        Tactic::Each(_) | Tactic::Once(_) => false,
        Tactic::Try(_)
        | Tactic::Repeat(_)
        | Tactic::Children(_)
        | Tactic::Into(..)
        | Tactic::Bu(_)
        | Tactic::Td(_)
        | Tactic::Id => false,
        Tactic::RepeatN(_, t) => can_fail(t),
        Tactic::Seq(ts) => ts.iter().any(can_fail),
        // A choice reports whatever the branch it ends on reported, so it can
        // only fail if that last branch can.
        Tactic::Choice(ts) => ts.last().is_none_or(can_fail),
    }
}

pub(crate) fn apply(t: &Tactic, env: &Env, nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    match t {
        Tactic::Id => Ok(Outcome::Unchanged(nodes)),
        Tactic::Fail => Ok(Outcome::Failed(nodes)),
        Tactic::Each(rules) => each(rules, env, nodes),
        Tactic::Once(rules) => once(rules, env, nodes),

        Tactic::At(i, rules) => {
            let mut nodes = nodes;
            Ok(if step(rules, env, &mut nodes, *i)?.is_some() {
                Outcome::Changed(nodes)
            } else {
                Outcome::Failed(nodes)
            })
        }

        Tactic::IntoAt(sel, i, inner) => {
            let mut nodes = nodes;
            let Some(node) = nodes.get_mut(*i) else {
                return Ok(Outcome::Failed(nodes));
            };
            let bodies = selected_bodies(node, *sel);
            if bodies.is_empty() {
                return Ok(Outcome::Failed(nodes));
            }
            let mut changed = false;
            let mut failed = false;
            for body in bodies {
                let outcome = apply(inner, env, std::mem::take(body))?;
                changed |= outcome.changed();
                failed |= matches!(outcome, Outcome::Failed(_));
                *body = outcome.into_nodes();
            }
            Ok(if failed {
                // The inner tactic's rollback contract already handed each
                // body back untouched, so the whole sequence is intact.
                Outcome::Failed(nodes)
            } else if changed {
                Outcome::Changed(nodes)
            } else {
                Outcome::Unchanged(nodes)
            })
        }

        Tactic::Try(inner) => Ok(match apply(inner, env, nodes)? {
            Outcome::Failed(n) => Outcome::Unchanged(n),
            other => other,
        }),

        Tactic::Seq(ts) => {
            // Only a member after the first needs a rollback copy: if the first
            // fails it has already handed the input back.
            let saved = ts
                .iter()
                .skip(1)
                .any(can_fail)
                .then(|| nodes.clone());
            let mut cur = nodes;
            let mut changed = false;
            for t in ts {
                match apply(t, env, cur)? {
                    Outcome::Changed(n) => {
                        cur = n;
                        changed = true;
                    }
                    Outcome::Unchanged(n) => cur = n,
                    Outcome::Failed(n) => return Ok(Outcome::Failed(saved.unwrap_or(n))),
                }
            }
            Ok(if changed {
                Outcome::Changed(cur)
            } else {
                Outcome::Unchanged(cur)
            })
        }

        Tactic::Choice(ts) => {
            // First branch that *does something*, not merely the first that
            // does not fail. The two coincide for `each`, which only ever
            // reports Changed or Failed — but every total tactic (`repeat`,
            // `bu`, `try`, `id`) reports Unchanged when it had no work, and
            // treating that as a win would make `a | b` unusable with any of
            // them. `annihilate | factoring` has to reach `factoring`.
            let mut cur = nodes;
            let mut last = None;
            for t in ts {
                match apply(t, env, cur)? {
                    changed @ Outcome::Changed(_) => return Ok(changed),
                    // Unchanged and Failed both hand the sequence back, so the
                    // next branch starts from the same place. No copy needed.
                    other => {
                        let failed = matches!(other, Outcome::Failed(_));
                        cur = other.into_nodes();
                        last = Some(failed);
                    }
                }
            }
            Ok(match last {
                // Only report failure if the branch we ended on actually failed.
                Some(true) | None => Outcome::Failed(cur),
                Some(false) => Outcome::Unchanged(cur),
            })
        }

        Tactic::Repeat(inner) => {
            let mut cur = nodes;
            let mut changed = false;
            loop {
                let outcome = apply(inner, env, cur)?;
                let progressed = outcome.changed();
                cur = outcome.into_nodes();
                if !progressed {
                    break;
                }
                changed = true;
            }
            Ok(if changed {
                Outcome::Changed(cur)
            } else {
                Outcome::Unchanged(cur)
            })
        }

        Tactic::RepeatN(n, inner) => {
            let mut cur = nodes;
            let mut changed = false;
            for _ in 0..*n {
                match apply(inner, env, cur)? {
                    Outcome::Changed(v) => {
                        cur = v;
                        changed = true;
                    }
                    // Stop early rather than spinning on a tactic that has
                    // nothing left to do.
                    Outcome::Unchanged(v) | Outcome::Failed(v) => {
                        cur = v;
                        break;
                    }
                }
            }
            Ok(if changed {
                Outcome::Changed(cur)
            } else {
                Outcome::Unchanged(cur)
            })
        }

        Tactic::Children(inner) => {
            let (nodes, changed) = map_child_seqs(nodes, &mut |n| apply(inner, env, n))?;
            Ok(if changed {
                Outcome::Changed(nodes)
            } else {
                Outcome::Unchanged(nodes)
            })
        }

        Tactic::Into(sel, inner) => {
            let (nodes, changed) =
                map_selected_seqs(nodes, *sel, &mut |n| apply(inner, env, n))?;
            Ok(if changed {
                Outcome::Changed(nodes)
            } else {
                Outcome::Unchanged(nodes)
            })
        }

        Tactic::Bu(inner) => bottom_up(inner, env, nodes),

        Tactic::Td(inner) => top_down(inner, env, nodes),
    }
}

/// `bu(t) = children(bu(t)); try(t)`.
///
/// The `try` is load-bearing. Without it `bu` would fail whenever `t` misses at
/// the root — which is nearly always — and `repeat(bu(X))` would stop after one
/// pass even though a child had changed.
fn bottom_up(t: &Tactic, env: &Env, nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    let (nodes, children_changed) = map_child_seqs(nodes, &mut |n| bottom_up(t, env, n))?;
    let outcome = apply(t, env, nodes)?;
    let here_changed = outcome.changed();
    let nodes = outcome.into_nodes();
    Ok(if children_changed || here_changed {
        Outcome::Changed(nodes)
    } else {
        Outcome::Unchanged(nodes)
    })
}

/// `td(t) = try(t); children(td(t))`.
///
/// Total for the same reason `bu` is, and the mirror of it. Note what that
/// means for a rule that *creates* children: `td` descends into the body it
/// just produced, so one pass runs all the way down. `bu` visits children
/// before touching this level, so anything it creates waits for the next pass.
/// That is the whole difference between `inline_all` and bounded inlining.
fn top_down(t: &Tactic, env: &Env, nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    let outcome = apply(t, env, nodes)?;
    let here_changed = outcome.changed();
    let nodes = outcome.into_nodes();
    let (nodes, children_changed) = map_child_seqs(nodes, &mut |n| top_down(t, env, n))?;
    Ok(if here_changed || children_changed {
        Outcome::Changed(nodes)
    } else {
        Outcome::Unchanged(nodes)
    })
}

/// Runs `f` over the child sequences `sel` picks out, in order.
///
/// The same walk as `map_child_seqs` with a narrower notion of "child", so a
/// node with no child of that kind is simply skipped.
fn map_selected_seqs(
    mut nodes: Vec<Node>,
    sel: Selector,
    f: &mut dyn FnMut(Vec<Node>) -> Result<Outcome, TacticError>,
) -> Result<(Vec<Node>, bool), TacticError> {
    let mut changed = false;

    for node in nodes.iter_mut() {
        for body in selected_bodies(node, sel) {
            let outcome = f(std::mem::take(body))?;
            changed |= outcome.changed();
            *body = outcome.into_nodes();
        }
    }

    Ok((nodes, changed))
}

/// Runs `f` over every child sequence of every node, in order.
fn map_child_seqs(
    mut nodes: Vec<Node>,
    f: &mut dyn FnMut(Vec<Node>) -> Result<Outcome, TacticError>,
) -> Result<(Vec<Node>, bool), TacticError> {
    let mut changed = false;

    for node in nodes.iter_mut() {
        for body in child_bodies(node) {
            let outcome = f(std::mem::take(body))?;
            changed |= outcome.changed();
            *body = outcome.into_nodes();
        }
    }

    Ok((nodes, changed))
}

/// Applies the rules at every position, left to right, until none matches.
///
/// **The scan discipline lives here and nowhere else.** After a rule splices at
/// window-start `w`, the scan resumes at `w - (width - 1)` rather than moving
/// on, which reproduces every cascade the hand-written passes used to spell
/// out: a width-1 rule re-applies to its own output, and a width-2 rule
/// reconsiders a moved node against its new neighbour.
fn each(rules: &[&'static dyn Rule], env: &Env, mut nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    let mut fired = false;
    let mut w = 0usize;

    while w < nodes.len() {
        match step(rules, env, &mut nodes, w)? {
            Some(next) => {
                w = next;
                fired = true;
            }
            None => w += 1,
        }
    }

    Ok(if fired {
        Outcome::Changed(nodes)
    } else {
        // Not `Failed`: having looked everywhere and found nothing to do is a
        // no-op, and reporting it as failure would abort any sequence this
        // appears in.
        Outcome::Unchanged(nodes)
    })
}

/// Applies the first rule that matches, at the first position it matches.
fn once(rules: &[&'static dyn Rule], env: &Env, mut nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    for w in 0..nodes.len() {
        if step(rules, env, &mut nodes, w)?.is_some() {
            return Ok(Outcome::Changed(nodes));
        }
    }
    Ok(Outcome::Unchanged(nodes))
}

/// Tries every rule at one position. On a hit, splices and returns where the
/// scan should resume.
fn step(
    rules: &[&'static dyn Rule],
    env: &Env,
    nodes: &mut Vec<Node>,
    w: usize,
) -> Result<Option<usize>, TacticError> {
    for rule in rules {
        let width = rule.width();
        if w + width > nodes.len() {
            continue;
        }
        let window = &nodes[w..w + width];
        let Some(replacement) = rule.rewrite(env.prog, window) else {
            continue;
        };
        env.spend()?;
        debug_assert!(
            replacement[..] != *window,
            "rule '{}' returned its input unchanged, which would not terminate",
            rule.name()
        );

        if env.check {
            // Learning an arity is fine; changing one is not. `inline` can
            // turn `None` into a number, because a `#[recursive]`-annotated
            // sentence has no inferable arity as a call but its expanded body
            // may well have one. What must never happen is two different
            // answers, or a rule making a known arity unknowable.
            let before = net(env, window);
            let after = net(env, &replacement);
            let broke = match (before, after) {
                (Some(a), Some(b)) => a != b,
                (Some(_), None) => true,
                (None, _) => false,
            };
            if broke {
                return Err(TacticError::NetChanged {
                    rule: rule.name(),
                    before,
                    after,
                });
            }
        }

        env.note(rule.name(), w);
        nodes.splice(w..w + width, replacement);
        return Ok(Some(w.saturating_sub(width - 1)));
    }
    Ok(None)
}

/// Net stack effect of a sequence, which every rule must preserve.
///
/// Deliberately *not* full arity: annihilating `pick 2; drop` legitimately
/// drops the demand for three values that only the pick made, so the input
/// requirement may fall. Net change may not move at all.
fn net(env: &Env, nodes: &[Node]) -> Option<i64> {
    let (inputs, outputs) = seq_arity(env.prog, nodes);
    outputs.map(|o| o - inputs)
}
