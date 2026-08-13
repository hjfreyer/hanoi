//! The search: what drives the matchers, and what it leaves behind.
//!
//! A tactic is a partial function on a node sequence. It either matches and
//! changes something, matches and changes nothing, or fails — and a tactic that
//! fails hands the sequence back exactly as it received it, which is what makes
//! rollback a matter of ownership rather than of copying.
//!
//! What is new is that running one **produces a script**. Every firing is
//! applied by [`crate::applier`] and recorded as a [`Step`] with an absolute
//! [`Location`], so a run leaves behind a derivation that reproduces it. The
//! engine never edits a tree itself.
//!
//! ## The invariant, in three parts
//!
//! The old rule was: *a tactic's result depends only on the sequence it is
//! given, never on where in the tree it is being applied.* That splits:
//!
//! 1. **Matchers stay position-blind.** [`Matcher::plan`] is a pure function of
//!    its window, and reports where it wants to rewrite relative to that window.
//! 2. **Only the driver knows the path.** It is threaded through the traversal
//!    in [`Env::path`] and used for exactly one thing: stamping absolute
//!    locations onto the steps it records.
//! 3. **The applier depends only on the tree and the step.** So replaying a
//!    recorded script against a fresh build reproduces the run's result exactly
//!    — which is the property `a_run_is_reproduced_by_its_own_script` asserts,
//!    and the reason the script can be trusted as a derivation.
//!
//! ## Local application, absolute record
//!
//! The traversal owns each sub-sequence as it visits it (`std::mem::take`, then
//! write back), so during a run the root tree is not reachable from where the
//! work happens. A firing is therefore applied to the sequence in hand, with a
//! location relative to *it*, while the step written into the script carries
//! the full path. The two agree by construction — same relative part, same
//! offset — and the replay test is what holds them to it.
//!
//! Ancestor indices cannot go stale in between: while the engine is inside a
//! child body every enclosing frame is suspended mid-iteration, so nothing can
//! splice an ancestor sequence until the traversal returns to it.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::fmt;

use crate::applier::{ApplyError, apply_step};
use crate::ir::{Node, Selector, child_seq, child_seqs, sketch_head};
use crate::location::selector_name;
use crate::matcher::Matcher;
use crate::program::Program;
use crate::rule::{Script, Step};

/// How many firings the trace remembers. Enough to read an oscillation off the
/// end of it, not enough to bury the error message.
const TRACE_WINDOW: usize = 24;

/// How many misses the report spells out before it starts counting them.
const MISSES_SHOWN: usize = 10;

/// What applying a tactic did.
///
/// `Failed` carries the sequence back out untouched. That is a contract, not a
/// convention: `Seq` and `Choice` rely on it to avoid cloning.
///
/// Note what does *not* fail: a matcher that matches nowhere reports
/// `Unchanged`. Scanning a sequence and finding no work is a successful no-op,
/// and treating it as an error would make `a; b` throw away everything `a` did
/// whenever `b` had nothing to do. `Failed` comes only from an explicit `fail`.
///
/// An *aimed* step that misses is `Unchanged` too, and additionally records a
/// [`Miss`]. That is deliberately not a fourth variant: a miss says the tactic
/// was written wrong, not that the run went differently, so nothing here has to
/// know about it.
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

/// A claim the tactic made that the tree did not bear out.
///
/// **An index is a claim; a scan is a question.** `at(9, sink)` says there is a
/// window at 9 and `then(3, t)` says the node at 3 has a then arm, where
/// `each(sink)` only asks whether anything fits. A question answered "nothing"
/// is an ordinary no-op — which is why a matcher that matches nowhere reports
/// `Unchanged`, and why it must — but a claim that does not hold is a mistyped
/// number, and it used to look exactly like a rule with nothing to do.
///
/// A miss is a **diagnostic rather than a failure**: the tree keeps whatever
/// the rest of the tactic did, so the listing that says which number to write
/// instead is printed beside the complaint. Nothing rolls back, and `must(t)`
/// is still how you ask for that.
///
/// Two things do not record one. A claim made inside a search is not a claim —
/// `bu(at(0, collapse))` is a sweep that happens to be aimed at every level it
/// visits, and the levels where it does not land are the answer rather than a
/// mistake — and neither is a claim in a `|` branch that a later branch took
/// over from, since offering an alternative is saying the first may miss.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Miss {
    /// What was aimed, as the tactic wrote it.
    aim: String,
    /// Why it did not land, in terms of what was there instead.
    why: String,
    /// Where the traversal was when it aimed.
    path: Vec<(usize, Selector)>,
}

impl fmt::Display for Miss {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} — {}",
            self.aim,
            where_it_aimed(&self.path),
            self.why
        )
    }
}

/// The sequence a miss happened in, named the way a location names it.
fn where_it_aimed(path: &[(usize, Selector)]) -> String {
    if path.is_empty() {
        return "at the root".to_string();
    }
    let legs: Vec<String> = path
        .iter()
        .map(|(i, sel)| format!("{}.{}", i, selector_name(*sel)))
        .collect();
    format!("in [{}]", legs.join(", "))
}

/// The misses of a run, as the lines the tool prints.
///
/// Empty when nothing missed, so the caller can use it to decide whether to
/// say anything at all — and, at the top level, whether to exit non-zero.
pub(crate) fn miss_report(misses: &[Miss]) -> Vec<String> {
    if misses.is_empty() {
        return Vec::new();
    }
    let mut out = vec![
        format!("{} aimed step(s) matched nothing:", misses.len()),
        String::new(),
    ];
    for miss in misses.iter().take(MISSES_SHOWN) {
        out.push(format!("  {}", miss));
    }
    if misses.len() > MISSES_SHOWN {
        out.push(format!("  ... and {} more", misses.len() - MISSES_SHOWN));
    }
    out.push(String::new());
    out.push(
        "  An aimed step names a position, so missing one is a mistyped number \
         rather"
            .to_string(),
    );
    out.push("  than a rule with nothing to do. The `pos` column of the listing is".to_string());
    out.push("  where the numbers are, and `try(...)` is how you say a miss is".to_string());
    out.push("  acceptable. Nothing was rolled back.".to_string());
    out
}

#[derive(Debug)]
pub(crate) enum TacticError {
    /// The budget ran out. Almost always an oscillation between two matchers
    /// that undo each other, which the recent-firings list makes obvious.
    OutOfFuel { spent: u64, recent: Vec<String> },
    /// A matcher proposed a step the applier would not take. This is always a
    /// bug in the matcher: it is required to check its own side conditions.
    Refused(ApplyError),
    /// The tactic failed, and nothing above it caught that.
    ///
    /// Only `fail` produces a failure — a matcher that matches nowhere reports
    /// "unchanged" — so reaching this means the tactic *asked* to fail: usually
    /// `must(...)`, which is how you say a step you aimed had better land.
    Failed,
}

impl std::fmt::Display for TacticError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TacticError::OutOfFuel { spent, recent } => {
                writeln!(f, "out of fuel after {} steps.", spent)?;
                writeln!(f)?;
                writeln!(f, "The last {} were:", recent.len())?;
                for r in recent {
                    writeln!(f, "  {}", r)?;
                }
                writeln!(f)?;
                write!(
                    f,
                    "A matcher alternating with its opposite looks exactly like \
                     this. `collapse` and `expand` are opposite readings of one \
                     law; so are `sink` and `float`, and `factor` and `unfactor`. \
                     Raise the budget with --fuel if the work is genuinely this \
                     large."
                )
            }
            TacticError::Refused(err) => write!(
                f,
                "a matcher proposed a step that does not apply, which is a bug \
                 in the matcher rather than in the script:\n  {}",
                err
            ),
            TacticError::Failed => write!(
                f,
                "the tactic failed, and the term is unchanged.\n\n  \
                 Only `fail` fails — a rule that matches nowhere is a no-op — so \
                 something asked for this. `must(t)` is the usual reason: it \
                 fails when `t` changes nothing, which is how an aimed step says \
                 it missed. Check the position, or drop the `must` to see where \
                 the term actually got."
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
    /// The derivation so far.
    script: RefCell<Script>,
    /// Where the traversal currently is, outermost first. Pushed on the way
    /// into a child sequence and popped on the way out.
    path: RefCell<Vec<(usize, Selector)>>,
    /// Aimed steps that did not land. See [`Miss`].
    misses: RefCell<Vec<Miss>>,
    /// How many searches the tactic is currently inside.
    ///
    /// A claim made inside one is not a claim, so this is what tells an aimed
    /// step whether missing is worth saying anything about.
    searching: Cell<usize>,
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
            script: RefCell::new(Vec::new()),
            path: RefCell::new(Vec::new()),
            misses: RefCell::new(Vec::new()),
            searching: Cell::new(0),
        }
    }

    /// The derivation this run produced.
    pub(crate) fn script(&self) -> Script {
        self.script.borrow().clone()
    }

    fn script_len(&self) -> usize {
        self.script.borrow().len()
    }

    /// Drops everything recorded since `mark`, for a branch that rolled back.
    ///
    /// Fuel is deliberately *not* refunded. The work was done; that it was
    /// thrown away is a fact about the search, and hiding it would make a
    /// thrashing tactic look cheap.
    fn truncate_script(&self, mark: usize) {
        self.script.borrow_mut().truncate(mark);
    }

    /// The aimed steps this run made that did not land.
    pub(crate) fn misses(&self) -> Vec<Miss> {
        self.misses.borrow().clone()
    }

    /// Records that an aimed step did not land, unless a search is asking.
    ///
    /// Deliberately *not* an [`Outcome`]. A miss changes nothing about what the
    /// tactic does, which is what lets it be reported without redesigning the
    /// outcome algebra around a fourth case — and what lets a run that missed
    /// still show the tree it produced, since that is the listing you need in
    /// order to fix the number.
    fn note_miss(&self, aim: String, why: String) {
        if self.searching.get() > 0 {
            return;
        }
        self.misses.borrow_mut().push(Miss {
            aim,
            why,
            path: self.path(),
        });
    }

    fn misses_len(&self) -> usize {
        self.misses.borrow().len()
    }

    /// Forgets the misses recorded in `from..to`, for a `|` branch that a later
    /// one took over from.
    fn drop_misses(&self, from: usize, to: usize) {
        self.misses.borrow_mut().drain(from..to);
    }

    /// Runs `f` in a search context, where an aimed step that misses is not
    /// making a claim.
    fn searching<T>(&self, f: impl FnOnce() -> T) -> T {
        self.searching.set(self.searching.get() + 1);
        let out = f();
        self.searching.set(self.searching.get() - 1);
        out
    }

    fn descend(&self, index: usize, sel: Selector) {
        self.path.borrow_mut().push((index, sel));
    }

    fn ascend(&self) {
        self.path.borrow_mut().pop();
    }

    fn path(&self) -> Vec<(usize, Selector)> {
        self.path.borrow().clone()
    }

    /// Charged once per *step*, globally across the run.
    ///
    /// Steps rather than firings, because a step is the unit of work the
    /// applier does and the unit a script holds. A firing that takes three
    /// steps costs three: `factor` is not free just because one matcher
    /// arranged it.
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

    fn note(&self, matcher: &'static str, step: &Step) {
        *self.hits.borrow_mut().entry(matcher).or_insert(0) += 1;
        let mut recent = self.recent.borrow_mut();
        if recent.len() == TRACE_WINDOW {
            recent.pop_front();
        }
        recent.push_back(format!("{} via {}", step, matcher));
    }

    /// Firing counts by matcher, most frequent first.
    pub(crate) fn histogram(&self) -> Vec<(&'static str, usize)> {
        let mut out: Vec<_> = self.hits.borrow().iter().map(|(k, v)| (*k, *v)).collect();
        out.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        out
    }

    pub(crate) fn steps_taken(&self) -> u64 {
        self.spent.get()
    }
}

#[derive(Debug)]
pub(crate) enum Tactic {
    /// Apply these matchers at every position, left to right, to exhaustion.
    ///
    /// Owned rather than borrowed, because a matcher may carry an argument:
    /// `introduce { pick 0 }` is a different matcher from `introduce { drop }`
    /// and neither exists until a tactic names it.
    Each(Vec<Box<dyn Matcher>>),
    /// Apply the first matcher that matches, at the first position it matches.
    Once(Vec<Box<dyn Matcher>>),
    /// Apply the first matcher that matches, at *exactly* this position.
    ///
    /// `once` finds the first place a rule fits; this one is told. Together
    /// with [`Tactic::IntoNth`] it can name any window a script can, which is
    /// what a listing's `[1.then, 2.body] @2` reads as.
    At(usize, Vec<Box<dyn Matcher>>),
    Seq(Vec<Tactic>),
    Choice(Vec<Tactic>),
    Try(Box<Tactic>),
    /// Fails unless the inner tactic changes something.
    ///
    /// The counterpart to `try`, and what makes an aimed step checkable: `at`
    /// and an indexed descent are silent when they miss, since a rule matching
    /// nowhere is an ordinary no-op. Wrapping one says the miss is an error.
    ///
    /// Exactly `t | fail`, which is how it is built.
    Must(Box<Tactic>),
    Repeat(Box<Tactic>),
    RepeatN(usize, Box<Tactic>),
    /// Apply to every child sequence, one level down. Never fails.
    Children(Box<Tactic>),
    /// Apply to one *kind* of child sequence, one level down. Never fails.
    ///
    /// `children` is this with every selector at once. Splitting them out is
    /// what lets a script open one branch arm and leave the other alone.
    Into(Selector, Box<Tactic>),
    /// Apply to *one* child of *one* node, named by index and kind.
    ///
    /// [`Tactic::Into`] reaches every branch's then arm; this reaches the then
    /// arm of the branch you meant. A node that is not there, or has no child
    /// of that kind, is left alone — the same stance `each` takes towards a
    /// matcher that matches nowhere.
    IntoNth(usize, Selector, Box<Tactic>),
    /// Children first, then here. Never fails.
    Bu(Box<Tactic>),
    /// Here first, then children. Never fails.
    ///
    /// The direction matters most for `unfold`: `td` opens a call and then
    /// descends into the body it just created, so one `td` pass expands the
    /// whole call graph. `bu` reaches new bodies only on the next pass, so
    /// `repeat_n(k, bu(each(unfold)))` is what gives you k levels.
    Td(Box<Tactic>),
    Id,
    Fail,
}

/// Whether a tactic can report `Failed`.
///
/// Used to decide whether `Seq` and `Choice` need to save a copy for rollback.
/// Since only an explicit `fail` can fail, nothing built from matchers clones.
fn can_fail(t: &Tactic) -> bool {
    match t {
        Tactic::Fail => true,
        Tactic::Must(_) => true,
        Tactic::Each(_) | Tactic::Once(_) | Tactic::At(..) => false,
        Tactic::Try(_)
        | Tactic::Repeat(_)
        | Tactic::Children(_)
        | Tactic::Into(..)
        | Tactic::IntoNth(..)
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
        Tactic::Each(ms) => each(ms, env, nodes),
        Tactic::Once(ms) => once(ms, env, nodes),
        Tactic::At(n, ms) => at(*n, ms, env, nodes),

        // A search, for the purpose of misses: `try` is the explicit way to say
        // that what is inside it may come to nothing.
        Tactic::Try(inner) => Ok(match env.searching(|| apply(inner, env, nodes))? {
            Outcome::Failed(n) => Outcome::Unchanged(n),
            other => other,
        }),

        Tactic::Must(inner) => {
            // The script goes back too, for the same reason `Seq` truncates:
            // a derivation must not describe work whose result was discarded.
            let mark = env.script_len();
            Ok(match apply(inner, env, nodes)? {
                changed @ Outcome::Changed(_) => changed,
                other => {
                    env.truncate_script(mark);
                    Outcome::Failed(other.into_nodes())
                }
            })
        }

        Tactic::Seq(ts) => {
            // Only a member after the first needs a rollback copy: if the first
            // fails it has already handed the input back.
            let saved = ts.iter().skip(1).any(can_fail).then(|| nodes.clone());
            let mark = env.script_len();
            let mut cur = nodes;
            let mut changed = false;
            for t in ts {
                match apply(t, env, cur)? {
                    Outcome::Changed(n) => {
                        cur = n;
                        changed = true;
                    }
                    Outcome::Unchanged(n) => cur = n,
                    Outcome::Failed(n) => {
                        // The tree goes back; so must the derivation, or the
                        // script would describe work the run did not keep.
                        env.truncate_script(mark);
                        return Ok(Outcome::Failed(saved.unwrap_or(n)));
                    }
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
            // does not fail. Every total tactic reports Unchanged when it had
            // no work, and treating that as a win would make `a | b` unusable
            // with any of them.
            //
            // No script bookkeeping here: a branch that changed nothing
            // recorded nothing, and a branch that changed something returns
            // immediately. A branch that changed-then-failed is itself a `Seq`,
            // which has already truncated.
            //
            // Misses do need it. Offering an alternative is saying the first
            // branch may miss, so once a later one has done something, what the
            // earlier ones aimed at was a candidate rather than a claim. Only
            // the ones before the winner go: its own inner misses stand, and so
            // do all of them when no branch changed anything — `t | fail` is
            // `must(t)`, and the reason it failed is the whole point.
            let start = env.misses_len();
            let mut cur = nodes;
            let mut last = None;
            for t in ts {
                let mark = env.misses_len();
                match apply(t, env, cur)? {
                    changed @ Outcome::Changed(_) => {
                        env.drop_misses(start, mark);
                        return Ok(changed);
                    }
                    other => {
                        let failed = matches!(other, Outcome::Failed(_));
                        cur = other.into_nodes();
                        last = Some(failed);
                    }
                }
            }
            Ok(match last {
                Some(true) | None => Outcome::Failed(cur),
                Some(false) => Outcome::Unchanged(cur),
            })
        }

        // Every arm from here to `td` is a search: it says where to look rather
        // than what has to be there, and the last turn of a `repeat` misses by
        // construction. An aimed step nested inside one is along for the ride.
        Tactic::Repeat(inner) => env.searching(|| {
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
        }),

        Tactic::RepeatN(n, inner) => env.searching(|| {
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
        }),

        Tactic::Children(inner) => {
            let (nodes, changed) = env
                .searching(|| map_children(nodes, env, None, &mut |n, env| apply(inner, env, n)))?;
            Ok(if changed {
                Outcome::Changed(nodes)
            } else {
                Outcome::Unchanged(nodes)
            })
        }

        Tactic::Into(sel, inner) => {
            let (nodes, changed) = env.searching(|| {
                map_children(nodes, env, Some(*sel), &mut |n, env| apply(inner, env, n))
            })?;
            Ok(if changed {
                Outcome::Changed(nodes)
            } else {
                Outcome::Unchanged(nodes)
            })
        }

        Tactic::IntoNth(index, sel, inner) => {
            let (nodes, changed) =
                map_one_child(nodes, env, *index, *sel, &mut |n, env| apply(inner, env, n))?;
            Ok(if changed {
                Outcome::Changed(nodes)
            } else {
                Outcome::Unchanged(nodes)
            })
        }

        Tactic::Bu(inner) => env.searching(|| bottom_up(inner, env, nodes)),

        Tactic::Td(inner) => env.searching(|| top_down(inner, env, nodes)),
    }
}

/// `bu(t) = children(bu(t)); try(t)`.
///
/// The `try` is load-bearing. Without it `bu` would fail whenever `t` misses at
/// the root — which is nearly always — and `repeat(bu(X))` would stop after one
/// pass even though a child had changed.
fn bottom_up(t: &Tactic, env: &Env, nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    let (nodes, children_changed) =
        map_children(nodes, env, None, &mut |n, env| bottom_up(t, env, n))?;
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
/// means for a matcher that *creates* children: `td` descends into the body it
/// just produced, so one pass runs all the way down.
fn top_down(t: &Tactic, env: &Env, nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    let outcome = apply(t, env, nodes)?;
    let here_changed = outcome.changed();
    let nodes = outcome.into_nodes();
    let (nodes, children_changed) =
        map_children(nodes, env, None, &mut |n, env| top_down(t, env, n))?;
    Ok(if here_changed || children_changed {
        Outcome::Changed(nodes)
    } else {
        Outcome::Unchanged(nodes)
    })
}

/// What a traversal does to each child sequence it reaches.
type Descend<'f> = &'f mut dyn FnMut(Vec<Node>, &Env) -> Result<Outcome, TacticError>;

/// Runs `f` over child sequences, in order, tracking where it went.
///
/// `sel` of `None` takes every child; `Some(s)` takes only children of that
/// kind, so a node with none is simply skipped — the same stance `each` takes
/// towards a matcher that matches nowhere.
///
/// The index pushed onto the path is the child's position *at the moment of
/// descent*, which is what makes the recorded locations right: this level
/// cannot be spliced while the traversal is below it.
fn map_children(
    mut nodes: Vec<Node>,
    env: &Env,
    sel: Option<Selector>,
    f: Descend,
) -> Result<(Vec<Node>, bool), TacticError> {
    let mut changed = false;

    for (index, node) in nodes.iter_mut().enumerate() {
        for (kind, body) in child_seqs(node) {
            if sel.is_some_and(|want| want != kind) {
                continue;
            }
            env.descend(index, kind);
            let outcome = f(std::mem::take(body), env);
            env.ascend();
            let outcome = outcome?;
            changed |= outcome.changed();
            *body = outcome.into_nodes();
        }
    }

    Ok((nodes, changed))
}

/// Applies the matchers at every position, left to right, until none matches.
///
/// **The scan discipline lives here and nowhere else.** After a firing at
/// window-start `w`, the scan resumes at `w - (width - 1)` rather than moving
/// on, which reproduces every cascade the hand-written passes used to spell
/// out: a width-1 matcher re-applies to its own output, and a width-2 matcher
/// reconsiders a moved node against its new neighbour.
fn each(
    matchers: &[Box<dyn Matcher>],
    env: &Env,
    mut nodes: Vec<Node>,
) -> Result<Outcome, TacticError> {
    let mut fired = false;
    let mut w = 0usize;

    while w < nodes.len() {
        match step(matchers, env, &mut nodes, w)? {
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
        Outcome::Unchanged(nodes)
    })
}

/// Applies the first matcher that matches, at exactly `n`.
///
/// No scan, and no failure either: a position past the end, or one where
/// nothing fits, hands the sequence back unchanged, so `at` composes in a
/// sequence like everything else and `a; b` keeps what `a` did.
///
/// It does not do so *silently*, though. Naming a position is a claim, and one
/// that does not hold is recorded as a [`Miss`] saying what was there instead.
/// That is a diagnostic rather than a rollback — see [`Env::note_miss`].
fn at(
    n: usize,
    matchers: &[Box<dyn Matcher>],
    env: &Env,
    mut nodes: Vec<Node>,
) -> Result<Outcome, TacticError> {
    if n < nodes.len() && step(matchers, env, &mut nodes, n)?.is_some() {
        return Ok(Outcome::Changed(nodes));
    }
    let names: Vec<&str> = matchers.iter().map(|m| m.name()).collect();
    env.note_miss(
        format!("at({}, {})", n, names.join(", ")),
        why_nothing_fits(matchers, &nodes, n),
    );
    Ok(Outcome::Unchanged(nodes))
}

/// Why an aimed rule did not fire, in terms of what was actually there.
///
/// Four different things look identical from outside — the sequence is too
/// short, the window runs off the end of it, the node is the wrong shape, or a
/// rule looked and declined — and a report that said only "matched nothing"
/// would leave the reader to work out which.
fn why_nothing_fits(matchers: &[Box<dyn Matcher>], nodes: &[Node], n: usize) -> String {
    if n >= nodes.len() {
        return match nodes.len() {
            0 => "that sequence is empty".to_string(),
            1 => "that sequence holds one node, at 0".to_string(),
            len => format!("that sequence holds {} nodes, 0 to {}", len, len - 1),
        };
    }
    let left = nodes.len() - n;
    let narrowest = matchers.iter().map(|m| m.width()).min().unwrap_or(1);
    if narrowest > left {
        return format!(
            "the window runs off the end: {} node(s) left there, and the \
             narrowest of those rules reads {}",
            left, narrowest
        );
    }
    format!("the node there is `{}`", sketch_head(&nodes[n]))
}

/// Applies the first matcher that matches, at the first position it matches.
fn once(
    matchers: &[Box<dyn Matcher>],
    env: &Env,
    mut nodes: Vec<Node>,
) -> Result<Outcome, TacticError> {
    for w in 0..nodes.len() {
        if step(matchers, env, &mut nodes, w)?.is_some() {
            return Ok(Outcome::Changed(nodes));
        }
    }
    Ok(Outcome::Unchanged(nodes))
}

/// Tries every matcher at one position. On a hit, applies what it planned and
/// returns where the scan should resume.
fn step(
    matchers: &[Box<dyn Matcher>],
    env: &Env,
    nodes: &mut Vec<Node>,
    w: usize,
) -> Result<Option<usize>, TacticError> {
    for matcher in matchers {
        let width = matcher.width();
        // The resume arithmetic below reads `width - 1`, and a matcher that
        // read no nodes would match at every position and never let `each`
        // advance. Matchers that size themselves from an argument check this
        // when they are built; this is where the invariant is written down.
        debug_assert!(width > 0, "`{}` reads no nodes", matcher.name());
        if w + width > nodes.len() {
            continue;
        }
        let Some(planned) = matcher.plan(env.prog, &nodes[w..w + width]) else {
            continue;
        };
        if planned.is_empty() {
            continue;
        }

        let path = env.path();
        for p in planned {
            env.spend()?;

            // Applied against the sequence in hand, recorded against the root.
            // The two differ only in the ancestry stamped on the front.
            let local = Step {
                kind: p.kind.clone(),
                dir: p.dir,
                loc: p.rel.under(&[], w),
            };
            let recorded = Step {
                kind: p.kind,
                dir: p.dir,
                loc: p.rel.under(&path, w),
            };

            apply_step(env.prog, nodes, &local, env.script_len(), env.check)
                .map_err(TacticError::Refused)?;

            env.note(matcher.name(), &recorded);
            env.script.borrow_mut().push(recorded);
        }
        return Ok(Some(w.saturating_sub(width - 1)));
    }
    Ok(None)
}

/// Runs `f` over one named child of one named node.
///
/// The index goes onto the path exactly as it does in [`map_children`], so a
/// step taken down here records the same location it would have if a sweep had
/// found it — which is what keeps `at` and `each` interchangeable as far as the
/// script is concerned.
///
/// A node that is not there, or has no child of that kind, is left alone and
/// recorded as a [`Miss`]: an index is a claim, the same way `at`'s is.
fn map_one_child(
    mut nodes: Vec<Node>,
    env: &Env,
    index: usize,
    sel: Selector,
    f: Descend,
) -> Result<(Vec<Node>, bool), TacticError> {
    let kind = selector_name(sel);
    let aim = || format!("{}({}, …)", kind, index);
    if index >= nodes.len() {
        env.note_miss(aim(), why_nothing_fits(&[], &nodes, index));
        return Ok((nodes, false));
    }
    if child_seq(&mut nodes[index], sel).is_none() {
        let what = sketch_head(&nodes[index]);
        env.note_miss(
            aim(),
            format!("the node there is `{}`, which has no {} part", what, kind),
        );
        return Ok((nodes, false));
    }
    let body = child_seq(&mut nodes[index], sel).expect("just looked");
    env.descend(index, sel);
    let outcome = f(std::mem::take(body), env);
    env.ascend();
    let outcome = outcome?;
    let changed = outcome.changed();
    *body = outcome.into_nodes();
    Ok((nodes, changed))
}

/// Runs a tactic over a tree and returns what it produced, with its derivation.
///
/// A tactic that fails is reported rather than swallowed. Nothing below here
/// treats `Failed` as an outcome worth returning — `try` is how you say a
/// failure is acceptable — so one arriving at the top means the tactic asked
/// for something it did not get.
pub(crate) fn run(
    env: &Env,
    tactic: &Tactic,
    tree: Vec<Node>,
) -> Result<(Vec<Node>, Script), TacticError> {
    match apply(tactic, env, tree)? {
        Outcome::Failed(_) => Err(TacticError::Failed),
        other => Ok((other.into_nodes(), env.script())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::applier::apply_script;
    use crate::ir::build;
    use crate::location::Location;
    use crate::matcher::{self, matcher_by_name};
    use bytecode::{Instruction, Library, Value, assemble};

    fn m(name: &str) -> Box<dyn Matcher> {
        matcher_by_name(name).unwrap_or_else(|| panic!("no matcher '{}'", name))
    }

    fn each_of(names: &[&str]) -> Tactic {
        Tactic::Each(names.iter().map(|n| m(n)).collect())
    }

    fn once_of(names: &[&str]) -> Tactic {
        Tactic::Once(names.iter().map(|n| m(n)).collect())
    }

    fn empty_prog() -> Program<'static> {
        Program::new(Box::leak(Box::new(Library::new())))
    }

    fn op(i: Instruction) -> Node {
        Node::Op(i)
    }

    fn dip(depth: usize, body: Vec<Node>) -> Node {
        Node::Dip {
            depth,
            origins: Vec::new(),
            body,
        }
    }

    fn branch(then_body: Vec<Node>, else_body: Vec<Node>) -> Node {
        Node::Branch {
            then_origin: "then".to_string(),
            then_body,
            else_origin: "else".to_string(),
            else_body,
        }
    }

    /// Runs a tactic and checks the script it produced reproduces it.
    ///
    /// Every test goes through this, so the replay invariant is not one test
    /// but a precondition of every assertion in the module.
    fn run_checked(prog: &Program, tactic: &Tactic, tree: Vec<Node>) -> (Vec<Node>, Script) {
        let env = Env::new(prog, 100_000, true);
        let before = tree.clone();
        let (after, script) = run(&env, tactic, tree).expect("tactic failed");

        let mut replayed = before;
        apply_script(prog, &mut replayed, &script, true)
            .unwrap_or_else(|e| panic!("the script did not replay: {}", e));
        assert_eq!(
            replayed, after,
            "replaying the script gave a different tree than the run"
        );
        (after, script)
    }

    // -- the headline invariant ---------------------------------------------

    #[test]
    fn a_run_is_reproduced_by_its_own_script() {
        // Deep, mixed work: rewrites at the root, inside a dip body, and inside
        // both branch arms, so the recorded paths have to be right in every
        // direction.
        let prog = empty_prog();
        let tree = vec![
            dip(1, vec![dip(2, vec![op(Instruction::Add)])]),
            branch(
                vec![dip(1, vec![dip(1, vec![op(Instruction::Not)])])],
                vec![
                    op(Instruction::Push(Value::Int(1))),
                    op(Instruction::Push(Value::Int(1))),
                    op(Instruction::Equal),
                ],
            ),
            dip(0, vec![op(Instruction::Drop)]),
        ];
        let tactic = Tactic::Repeat(Box::new(Tactic::Bu(Box::new(each_of(&[
            "collapse", "flatten", "eval2",
        ])))));
        let (after, script) = run_checked(&prog, &tactic, tree);

        // And it really did work in all three places.
        assert!(script.len() >= 3, "script was {:?}", script);
        assert_eq!(after[0], dip(3, vec![op(Instruction::Add)]));
    }

    #[test]
    fn a_recorded_location_names_the_arm_it_worked_in() {
        let prog = empty_prog();
        let tree = vec![branch(
            vec![op(Instruction::Add)],
            vec![dip(1, vec![dip(1, vec![])])],
        )];
        let (_, script) = run_checked(&prog, &tree_collapse(), tree);
        assert_eq!(script.len(), 1);
        assert_eq!(
            script[0].loc,
            Location {
                descent: vec![(0, Selector::Else)],
                at: 0
            }
        );
        assert_eq!(script[0].loc.to_string(), "[0.else] @0");
    }

    fn tree_collapse() -> Tactic {
        Tactic::Bu(Box::new(each_of(&["collapse"])))
    }

    // -- aiming -------------------------------------------------------------

    #[test]
    fn a_tactic_can_name_exactly_the_location_a_script_prints() {
        // The property that makes the two halves of addressing fit together:
        // what you write to reach a window is what the derivation says it
        // reached.
        let prog = empty_prog();
        let tree = vec![
            op(Instruction::Add),
            branch(
                vec![
                    op(Instruction::Not),
                    dip(1, vec![op(Instruction::Drop), dip(1, vec![dip(1, vec![])])]),
                ],
                Vec::new(),
            ),
        ];
        let tactic = Tactic::IntoNth(
            1,
            Selector::Then,
            Box::new(Tactic::IntoNth(
                1,
                Selector::Body,
                Box::new(Tactic::At(1, vec![m("collapse")])),
            )),
        );
        let (_, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(script.len(), 1);
        assert_eq!(script[0].loc.to_string(), "[1.then, 1.body] @1");
    }

    #[test]
    fn at_applies_only_where_it_is_told() {
        let prog = empty_prog();
        let tree = || {
            vec![
                dip(1, vec![dip(1, Vec::new())]),
                dip(1, vec![dip(1, Vec::new())]),
            ]
        };
        // Position 1, not position 0, even though both would match.
        let (after, script) = run_checked(&prog, &Tactic::At(1, vec![m("collapse")]), tree());
        assert_eq!(script.len(), 1);
        assert_eq!(script[0].loc, Location::root(1));
        assert_eq!(after[0], dip(1, vec![dip(1, Vec::new())]));
        assert_eq!(after[1], dip(2, Vec::new()));

        // Where `once` would have taken the first.
        let (_, script) = run_checked(&prog, &Tactic::Once(vec![m("collapse")]), tree());
        assert_eq!(script[0].loc, Location::root(0));
    }

    #[test]
    fn at_fires_once_rather_than_scanning_onward() {
        // Three nested frames: `at` collapses the pair it was pointed at and
        // stops, where `each` would cascade.
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, vec![dip(1, Vec::new())])])];
        let (_, script) = run_checked(&prog, &Tactic::At(0, vec![m("collapse")]), tree);
        assert_eq!(script.len(), 1);
    }

    #[test]
    fn a_position_that_is_not_there_is_a_no_op() {
        // Aiming badly is something the listing tells you, not something that
        // aborts a sequence.
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, Vec::new())])];
        let env = Env::new(&prog, 1000, true);
        let outcome = apply(&Tactic::At(7, vec![m("collapse")]), &env, tree.clone()).unwrap();
        assert!(matches!(outcome, Outcome::Unchanged(_)));
        assert!(env.script().is_empty());
    }

    #[test]
    fn an_indexed_descent_leaves_its_siblings_alone() {
        let prog = empty_prog();
        let inner = || dip(1, vec![dip(1, Vec::new())]);
        let tree = vec![
            branch(vec![inner()], vec![inner()]),
            branch(vec![inner()], vec![inner()]),
        ];
        let tactic = Tactic::IntoNth(
            1,
            Selector::Then,
            Box::new(Tactic::Each(vec![m("collapse")])),
        );
        let (after, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(script.len(), 1, "it reached more than the one arm");
        assert_eq!(script[0].loc.to_string(), "[1.then] @0");
        // The first branch, and the second's else arm, are untouched.
        let [
            Node::Branch { then_body: a, .. },
            Node::Branch {
                then_body: b,
                else_body: c,
                ..
            },
        ] = &after[..]
        else {
            panic!("expected two branches")
        };
        assert_eq!(a, &vec![inner()]);
        assert_eq!(b, &vec![dip(2, Vec::new())]);
        assert_eq!(c, &vec![inner()]);
    }

    #[test]
    fn an_indexed_descent_into_the_wrong_kind_of_node_is_a_no_op() {
        let prog = empty_prog();
        // Node 0 is a dip: it has a body, not a then arm.
        let tree = vec![dip(1, vec![dip(1, Vec::new())])];
        let env = Env::new(&prog, 1000, true);
        let tactic = Tactic::IntoNth(
            0,
            Selector::Then,
            Box::new(Tactic::Each(vec![m("collapse")])),
        );
        let outcome = apply(&tactic, &env, tree).unwrap();
        assert!(matches!(outcome, Outcome::Unchanged(_)));

        // And an index past the end.
        let env = Env::new(&prog, 1000, true);
        let tactic = Tactic::IntoNth(
            9,
            Selector::Body,
            Box::new(Tactic::Each(vec![m("collapse")])),
        );
        let outcome = apply(&tactic, &env, vec![dip(1, vec![dip(1, Vec::new())])]).unwrap();
        assert!(matches!(outcome, Outcome::Unchanged(_)));
    }

    #[test]
    fn must_fails_when_the_aim_misses_and_passes_when_it_lands() {
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, Vec::new())])];

        let hit = Tactic::Must(Box::new(Tactic::At(0, vec![m("collapse")])));
        let (after, script) = run_checked(&prog, &hit, tree.clone());
        assert_eq!(after, vec![dip(2, Vec::new())]);
        assert_eq!(script.len(), 1);

        // Same rule, wrong position: silent on its own, an error under `must`.
        let miss = Tactic::At(5, vec![m("collapse")]);
        let env = Env::new(&prog, 1000, true);
        assert!(matches!(
            apply(&miss, &env, tree.clone()).unwrap(),
            Outcome::Unchanged(_)
        ));

        let env = Env::new(&prog, 1000, true);
        let guarded = Tactic::Must(Box::new(miss));
        assert!(matches!(
            apply(&guarded, &env, tree.clone()).unwrap(),
            Outcome::Failed(_)
        ));
    }

    #[test]
    fn a_failure_reaching_the_top_is_reported_rather_than_swallowed() {
        // The whole point of `must`: a tactic that did not do what it said
        // has to be loud, or aiming is unverifiable.
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tactic = Tactic::Must(Box::new(Tactic::At(5, vec![m("collapse")])));
        let err = run(&env, &tactic, vec![dip(1, vec![dip(1, Vec::new())])]).unwrap_err();
        assert!(matches!(err, TacticError::Failed));
        assert!(err.to_string().contains("must"), "{}", err);
    }

    #[test]
    fn must_hands_back_the_term_and_the_script_untouched() {
        // A failure is a rollback, so neither the tree nor the derivation may
        // keep anything the failed branch did.
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tree = vec![dip(1, vec![dip(1, Vec::new())]), op(Instruction::Add)];
        // The collapse lands, but the sequence then demands something absent.
        let tactic = Tactic::Must(Box::new(Tactic::Seq(vec![
            Tactic::At(0, vec![m("collapse")]),
            Tactic::At(9, vec![m("collapse")]),
            Tactic::Fail,
        ])));
        let outcome = apply(&tactic, &env, tree.clone()).unwrap();
        assert!(matches!(outcome, Outcome::Failed(_)));
        assert_eq!(outcome.into_nodes(), tree);
        assert!(env.script().is_empty(), "script kept {:?}", env.script());
    }

    #[test]
    fn must_is_exactly_choice_with_fail() {
        // It is sugar, and saying so keeps the two from drifting.
        let prog = empty_prog();
        let tree = || vec![dip(1, vec![dip(1, Vec::new())])];
        for at in [0usize, 5] {
            let sugar = Tactic::Must(Box::new(Tactic::At(at, vec![m("collapse")])));
            let spelled = Tactic::Choice(vec![Tactic::At(at, vec![m("collapse")]), Tactic::Fail]);
            let a = Env::new(&prog, 1000, true);
            let b = Env::new(&prog, 1000, true);
            let ra = apply(&sugar, &a, tree()).unwrap();
            let rb = apply(&spelled, &b, tree()).unwrap();
            assert_eq!(
                matches!(ra, Outcome::Failed(_)),
                matches!(rb, Outcome::Failed(_)),
                "at {} they disagreed",
                at
            );
            assert_eq!(ra.into_nodes(), rb.into_nodes());
            assert_eq!(a.script().len(), b.script().len());
        }
    }

    // -- misses: an index is a claim ----------------------------------------

    /// The misses a tactic leaves behind, as the strings they print as.
    fn misses_of(prog: &Program, tactic: &Tactic, tree: Vec<Node>) -> Vec<String> {
        let env = Env::new(prog, 1000, true);
        apply(tactic, &env, tree).expect("the tactic errored");
        env.misses().iter().map(|m| m.to_string()).collect()
    }

    #[test]
    fn an_aimed_step_that_misses_says_what_was_there() {
        let prog = empty_prog();
        let tree = || vec![dip(1, vec![dip(1, Vec::new())]), op(Instruction::Add)];

        // Past the end: the sequence's size is the answer.
        let got = misses_of(&prog, &Tactic::At(9, vec![m("collapse")]), tree());
        assert_eq!(got.len(), 1, "{:?}", got);
        assert!(
            got[0].starts_with("at(9, collapse) at the root"),
            "{}",
            got[0]
        );
        assert!(got[0].contains("holds 2 nodes, 0 to 1"), "{}", got[0]);

        // In range, wrong shape: what is there is the answer.
        let got = misses_of(&prog, &Tactic::At(1, vec![m("collapse")]), tree());
        assert_eq!(got.len(), 1, "{:?}", got);
        assert!(got[0].contains("the node there is `add`"), "{}", got[0]);

        // In range, but the window runs off the end. `fuse` reads two nodes and
        // there is one left, which is a different mistake from either above.
        let got = misses_of(&prog, &Tactic::At(1, vec![m("fuse")]), tree());
        assert_eq!(got.len(), 1, "{:?}", got);
        assert!(got[0].contains("runs off the end"), "{}", got[0]);
    }

    #[test]
    fn an_indexed_descent_that_misses_names_the_part_it_wanted() {
        let prog = empty_prog();
        let inner = || Box::new(Tactic::Each(vec![m("collapse")]));

        // A dip has a body, not a then arm.
        let tree = vec![dip(1, vec![dip(1, Vec::new())])];
        let got = misses_of(&prog, &Tactic::IntoNth(0, Selector::Then, inner()), tree);
        assert_eq!(got.len(), 1, "{:?}", got);
        assert!(got[0].starts_with("then(0, …)"), "{}", got[0]);
        assert!(got[0].contains("no then part"), "{}", got[0]);

        // And an index past the end of the sequence.
        let tree = vec![dip(1, vec![dip(1, Vec::new())])];
        let got = misses_of(&prog, &Tactic::IntoNth(9, Selector::Body, inner()), tree);
        assert_eq!(got.len(), 1, "{:?}", got);
        assert!(got[0].contains("holds one node, at 0"), "{}", got[0]);
    }

    #[test]
    fn a_miss_names_the_sequence_it_happened_in() {
        // The path is the other half of the address, so a miss two levels down
        // has to say which two levels.
        let prog = empty_prog();
        let tree = vec![branch(vec![dip(1, vec![op(Instruction::Add)])], Vec::new())];
        let tactic = Tactic::IntoNth(
            0,
            Selector::Then,
            Box::new(Tactic::IntoNth(
                0,
                Selector::Body,
                Box::new(Tactic::At(4, vec![m("collapse")])),
            )),
        );
        let got = misses_of(&prog, &tactic, tree);
        assert_eq!(got.len(), 1, "{:?}", got);
        assert!(got[0].contains("in [0.then, 0.body]"), "{}", got[0]);
    }

    #[test]
    fn a_claim_made_inside_a_search_is_not_a_claim() {
        // `bu(at(0, collapse))` is a sweep that happens to be aimed at every
        // level it visits. The levels where it does not land are the answer,
        // not a mistyped number, and reporting them would drown the report.
        let prog = empty_prog();
        let tree = || {
            vec![
                dip(1, vec![dip(1, vec![op(Instruction::Add)])]),
                op(Instruction::Not),
            ]
        };
        let aimed = || Tactic::At(0, vec![m("collapse")]);
        for tactic in [
            Tactic::Bu(Box::new(aimed())),
            Tactic::Td(Box::new(aimed())),
            Tactic::Children(Box::new(aimed())),
            Tactic::Into(Selector::Body, Box::new(aimed())),
            Tactic::Try(Box::new(Tactic::At(9, vec![m("collapse")]))),
            Tactic::Repeat(Box::new(aimed())),
            Tactic::RepeatN(3, Box::new(aimed())),
        ] {
            let got = misses_of(&prog, &tactic, tree());
            assert!(got.is_empty(), "{:?} reported {:?}", tactic, got);
        }

        // Bare, the same aim is a claim — and this one holds, so it is silent
        // for the ordinary reason.
        let got = misses_of(&prog, &aimed(), tree());
        assert!(got.is_empty(), "{:?}", got);
        let got = misses_of(&prog, &Tactic::At(1, vec![m("collapse")]), tree());
        assert_eq!(got.len(), 1, "{:?}", got);
    }

    #[test]
    fn an_alternative_taking_over_means_the_earlier_aim_was_a_candidate() {
        let prog = empty_prog();
        let tree = || vec![op(Instruction::Add), dip(1, vec![dip(1, Vec::new())])];

        // The second branch does something, so the first was offered rather
        // than claimed.
        let tactic = Tactic::Choice(vec![
            Tactic::At(9, vec![m("collapse")]),
            Tactic::At(1, vec![m("collapse")]),
        ]);
        assert!(misses_of(&prog, &tactic, tree()).is_empty());

        // Nothing took over, so both stand.
        let tactic = Tactic::Choice(vec![
            Tactic::At(9, vec![m("collapse")]),
            Tactic::At(0, vec![m("collapse")]),
        ]);
        assert_eq!(misses_of(&prog, &tactic, tree()).len(), 2);
    }

    #[test]
    fn must_keeps_the_reason_it_failed() {
        // `must` rolls the tree and the script back; the miss is not work, it
        // is the explanation, and throwing it away would leave the failure
        // saying only that something did not happen.
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tactic = Tactic::Must(Box::new(Tactic::At(5, vec![m("collapse")])));
        let outcome = apply(&tactic, &env, vec![dip(1, vec![dip(1, Vec::new())])]).unwrap();
        assert!(matches!(outcome, Outcome::Failed(_)));
        let misses = env.misses();
        assert_eq!(misses.len(), 1, "{:?}", misses);
        assert!(misses[0].to_string().contains("at(5, collapse)"));
    }

    #[test]
    fn a_miss_rolls_nothing_back() {
        // The whole point of reporting rather than failing: the tree still
        // shows what the rest of the tactic did, which is the listing you need
        // in order to fix the number.
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tree = vec![dip(1, vec![dip(1, Vec::new())])];
        let tactic = Tactic::Seq(vec![
            Tactic::At(0, vec![m("collapse")]),
            Tactic::At(9, vec![m("collapse")]),
        ]);
        let outcome = apply(&tactic, &env, tree).unwrap();
        assert!(matches!(outcome, Outcome::Changed(_)));
        assert_eq!(outcome.into_nodes(), vec![dip(2, Vec::new())]);
        assert_eq!(env.script().len(), 1);
        assert_eq!(env.misses().len(), 1);
    }

    #[test]
    fn the_report_is_bounded() {
        let prog = empty_prog();
        let tactic = Tactic::Seq(
            (0..MISSES_SHOWN + 3)
                .map(|_| Tactic::At(9, vec![m("collapse")]))
                .collect(),
        );
        let env = Env::new(&prog, 1000, true);
        apply(&tactic, &env, vec![op(Instruction::Add)]).unwrap();
        let misses = env.misses();
        assert_eq!(misses.len(), MISSES_SHOWN + 3);
        let report = miss_report(&misses);
        assert!(report[0].contains(&format!("{} aimed", MISSES_SHOWN + 3)));
        assert!(
            report.iter().any(|l| l.contains("and 3 more")),
            "{:?}",
            report
        );
    }

    #[test]
    fn try_still_catches_what_must_throws() {
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tactic = Tactic::Try(Box::new(Tactic::Must(Box::new(Tactic::At(
            5,
            vec![m("collapse")],
        )))));
        assert!(matches!(
            apply(&tactic, &env, vec![dip(1, Vec::new())]).unwrap(),
            Outcome::Unchanged(_)
        ));
    }

    // -- scan discipline ----------------------------------------------------

    #[test]
    fn a_cascade_reconsiders_what_a_firing_moved() {
        // Three nested dips collapse to one, which needs the scan to come back
        // to a position it already passed.
        let prog = empty_prog();
        let tree = vec![dip(
            1,
            vec![dip(1, vec![dip(1, vec![op(Instruction::Add)])])],
        )];
        let tactic = Tactic::Repeat(Box::new(Tactic::Bu(Box::new(each_of(&["collapse"])))));
        let (after, _) = run_checked(&prog, &tactic, tree);
        assert_eq!(after, vec![dip(3, vec![op(Instruction::Add)])]);
    }

    #[test]
    fn each_keeps_going_after_a_firing_shortens_the_sequence() {
        let prog = empty_prog();
        let tree = vec![
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Drop),
            op(Instruction::Push(Value::Int(2))),
            op(Instruction::Drop),
        ];
        let (after, script) = run_checked(&prog, &each_of(&["annihilate"]), tree);
        assert_eq!(after, Vec::new());
        assert_eq!(script.len(), 2);
    }

    // -- the outcome algebra ------------------------------------------------

    #[test]
    fn a_matcher_that_finds_nothing_is_not_a_failure() {
        // `a; b` must not throw away what `a` did merely because `b` had
        // nothing to do.
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, vec![])])];
        let tactic = Tactic::Seq(vec![each_of(&["collapse"]), each_of(&["cancel_tuple"])]);
        let (after, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(after, vec![dip(2, vec![])]);
        assert_eq!(script.len(), 1);
    }

    #[test]
    fn choice_falls_through_a_branch_that_changed_nothing() {
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, vec![])])];
        let tactic = Tactic::Choice(vec![each_of(&["cancel_tuple"]), each_of(&["collapse"])]);
        let (after, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(after, vec![dip(2, vec![])]);
        assert_eq!(script.len(), 1);
    }

    #[test]
    fn try_repeat_bu_and_children_are_total() {
        let prog = empty_prog();
        let tree = vec![op(Instruction::Add)];
        for tactic in [
            Tactic::Try(Box::new(Tactic::Fail)),
            Tactic::Repeat(Box::new(each_of(&["collapse"]))),
            Tactic::Bu(Box::new(each_of(&["collapse"]))),
            Tactic::Td(Box::new(each_of(&["collapse"]))),
            Tactic::Children(Box::new(each_of(&["collapse"]))),
            Tactic::Into(Selector::Then, Box::new(each_of(&["collapse"]))),
        ] {
            let env = Env::new(&prog, 1000, true);
            let outcome = apply(&tactic, &env, tree.clone()).unwrap();
            assert!(
                !matches!(outcome, Outcome::Failed(_)),
                "{:?} failed on a sequence it had no work in",
                tactic
            );
        }
    }

    #[test]
    fn repeat_n_stops_early_when_there_is_nothing_left() {
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, vec![])])];
        let tactic = Tactic::RepeatN(50, Box::new(Tactic::Bu(Box::new(each_of(&["collapse"])))));
        let (_, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(script.len(), 1, "it kept going after the work ran out");
    }

    #[test]
    fn the_three_selectors_partition_children() {
        let prog = empty_prog();
        let tree = || {
            vec![
                branch(
                    vec![dip(1, vec![dip(1, vec![])])],
                    vec![dip(1, vec![dip(1, vec![])])],
                ),
                dip(1, vec![dip(1, vec![dip(1, vec![])])]),
            ]
        };
        let inner = || each_of(&["collapse"]);
        let all = Tactic::Children(Box::new(inner()));
        let split = Tactic::Seq(vec![
            Tactic::Into(Selector::Then, Box::new(inner())),
            Tactic::Into(Selector::Else, Box::new(inner())),
            Tactic::Into(Selector::Body, Box::new(inner())),
        ]);
        let (a, _) = run_checked(&prog, &all, tree());
        let (b, _) = run_checked(&prog, &split, tree());
        assert_eq!(a, b);
    }

    #[test]
    fn then_and_else_each_reach_one_arm_and_leave_the_other() {
        let prog = empty_prog();
        let tree = vec![branch(
            vec![dip(1, vec![dip(1, vec![])])],
            vec![dip(1, vec![dip(1, vec![])])],
        )];
        let tactic = Tactic::Into(Selector::Then, Box::new(each_of(&["collapse"])));
        let (after, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(script.len(), 1);
        let [
            Node::Branch {
                then_body,
                else_body,
                ..
            },
        ] = &after[..]
        else {
            panic!("expected a branch")
        };
        assert_eq!(then_body, &vec![dip(2, vec![])]);
        assert_eq!(else_body, &vec![dip(1, vec![dip(1, vec![])])]);
    }

    // -- rollback -----------------------------------------------------------

    #[test]
    fn a_failing_sequence_rolls_back_the_tree_and_the_script_together() {
        // This is the one place the two could diverge: if the tree goes back
        // but the script does not, the script describes work that was undone.
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, vec![])])];
        let tactic = Tactic::Try(Box::new(Tactic::Seq(vec![
            each_of(&["collapse"]),
            Tactic::Fail,
        ])));
        let (after, script) = run_checked(&prog, &tactic, tree.clone());
        assert_eq!(after, tree, "the tree did not roll back");
        assert!(script.is_empty(), "the script kept {:?}", script);
    }

    #[test]
    fn rollback_keeps_the_work_that_came_before_it() {
        let prog = empty_prog();
        let tree = vec![dip(1, vec![dip(1, vec![])]), dip(1, vec![dip(1, vec![])])];
        // One collapse survives; the failing sequence after it does not.
        let tactic = Tactic::Seq(vec![
            once_of(&["collapse"]),
            Tactic::Try(Box::new(Tactic::Seq(vec![
                once_of(&["collapse"]),
                Tactic::Fail,
            ]))),
        ]);
        let (_, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(script.len(), 1);
    }

    #[test]
    fn rollback_does_not_refund_fuel() {
        // The work happened. Hiding that would make a thrashing tactic look
        // cheap, and the budget is a measure of work rather than of progress.
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tactic = Tactic::Try(Box::new(Tactic::Seq(vec![
            each_of(&["collapse"]),
            Tactic::Fail,
        ])));
        apply(&tactic, &env, vec![dip(1, vec![dip(1, vec![])])]).unwrap();
        assert_eq!(env.steps_taken(), 1);
        assert!(env.script().is_empty());
    }

    // -- fuel ---------------------------------------------------------------

    #[test]
    fn a_multi_step_firing_costs_what_it_spends() {
        // `factor` is three steps, and the budget says so. It is not free
        // because one matcher arranged it.
        let prog = empty_prog();
        let env = Env::new(&prog, 1000, true);
        let tree = vec![branch(
            vec![op(Instruction::Add), op(Instruction::Drop)],
            vec![op(Instruction::Add), op(Instruction::Not)],
        )];
        let (_, script) = run(&env, &once_of(&["factor"]), tree).unwrap();
        assert_eq!(script.len(), 3);
        assert_eq!(env.steps_taken(), 3);
        // One firing, though, as far as the trace is concerned.
        assert_eq!(env.histogram(), vec![("factor", 3)]);
    }

    #[test]
    fn opposite_readings_of_one_law_exhaust_the_budget_and_say_so() {
        let prog = empty_prog();
        let env = Env::new(&prog, 20, true);
        let tactic = Tactic::Repeat(Box::new(Tactic::Bu(Box::new(each_of(&[
            "collapse", "expand",
        ])))));
        let err = apply(&tactic, &env, vec![dip(3, vec![op(Instruction::Add)])]).unwrap_err();
        let TacticError::OutOfFuel { recent, .. } = &err else {
            panic!("expected the budget to run out, got {:?}", err)
        };
        assert!(!recent.is_empty());
        assert!(err.to_string().contains("collapse"));
    }

    // -- against the real corpus --------------------------------------------

    #[test]
    fn a_corpus_sentence_replays_step_for_step() {
        let Some(library) = corpus() else { return };
        let prog = Program::new(library);

        let mut checked = 0;
        for (idx, _) in library.sentences.iter_enumerated() {
            let tree = build(library, idx);
            if tree.is_empty() {
                continue;
            }
            let tactic = Tactic::Repeat(Box::new(Tactic::Bu(Box::new(each_of(&[
                "collapse",
                "flatten",
                "fuse",
                "sink",
                "annihilate",
                "annihilate_flagged",
                "counit",
                "eval1",
                "eval2",
                "fold_branch",
                "factor",
                "cancel_tuple",
                "copy_const",
            ])))));
            let env = Env::new(&prog, 200_000, true);
            let before = tree.clone();
            let Ok((after, script)) = run(&env, &tactic, tree) else {
                continue;
            };
            if script.is_empty() {
                continue;
            }
            let mut replayed = before;
            apply_script(&prog, &mut replayed, &script, true)
                .unwrap_or_else(|e| panic!("#{} did not replay: {}", usize::from(idx), e));
            assert_eq!(
                replayed,
                after,
                "#{} replayed differently",
                usize::from(idx)
            );
            checked += 1;
        }
        assert!(
            checked > 50,
            "only {} corpus sentences did any work; the sweep is near-vacuous",
            checked
        );
    }

    fn corpus() -> Option<&'static Library> {
        let path = std::path::Path::new("../tests/main.hana");
        let code = std::fs::read_to_string(path).ok()?;
        let library = bytecode::assemble_with_path(&code, path.parent()).ok()?;
        Some(Box::leak(Box::new(library)))
    }

    #[test]
    fn unfolding_reaches_across_a_call_the_way_it_used_to() {
        // The classic: a jump hides a branch from the operator after it, and
        // opening it puts the two in one window.
        let library: &'static Library = Box::leak(Box::new(
            assemble(
                r#"
                sentence inner { push true branch { push 1 } { push 2 } }
                sentence outer { jump inner }
                "#,
            )
            .unwrap(),
        ));
        let prog = Program::new(library);
        let outer = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "outer")
            .map(|(i, _)| i)
            .unwrap();

        let tree = build(library, outer);
        let tactic = Tactic::Repeat(Box::new(Tactic::Td(Box::new(each_of(&[
            "unfold",
            "flatten",
            "fold_branch",
        ])))));
        let (after, script) = run_checked(&prog, &tactic, tree);
        assert_eq!(after, vec![op(Instruction::Push(Value::Int(1)))]);
        assert!(script.iter().any(|s| s.kind.name() == "unfold"));
    }

    #[test]
    fn every_matcher_can_be_placed_in_a_tactic() {
        // A registry that names something a tactic cannot hold would be a
        // silent hole in the language. `once` rather than `each`, because
        // placement is the question here and the matchers with no measure
        // deliberately do not settle — see below.
        let prog = empty_prog();
        for name in matcher::matcher_names() {
            let env = Env::new(&prog, 100, true);
            let tactic = once_of(&[name]);
            apply(&tactic, &env, vec![op(Instruction::Add)])
                .unwrap_or_else(|e| panic!("{} could not be placed: {}", name, e));
        }
    }

    #[test]
    fn a_matcher_that_rebuilds_its_own_window_does_not_settle() {
        // `swap` puts a `roll 1` in front of the operator it matched, and the
        // operator is still there — so `each` finds it again one along. That is
        // the same shape as `introduce`, and the reason both say to aim rather
        // than sweep. The budget is what says so out loud.
        let prog = empty_prog();
        let env = Env::new(&prog, 40, true);
        let err = apply(&each_of(&["swap"]), &env, vec![op(Instruction::Add)]).unwrap_err();
        assert!(matches!(err, TacticError::OutOfFuel { .. }), "{:?}", err);

        // Aimed, it does exactly one thing.
        let (after, script) = run_checked(&prog, &once_of(&["swap"]), vec![op(Instruction::Add)]);
        assert_eq!(script.len(), 1);
        assert_eq!(after, vec![op(Instruction::Roll(1)), op(Instruction::Add)]);
    }
}
