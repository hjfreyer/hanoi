//! The driver, as data: tactics over the table in [`rules`] and the
//! queries in [`query`], run into a [`Derivation`].
//!
//! There was a `saturate` in [`rules`] — a worklist that ran a list of laws
//! to fixpoint — and it was deleted on purpose: *which* laws, *where*, and
//! *in what order* is a strategy, and a strategy belongs to whoever is
//! proving something. This module is where a strategy is **written**: a
//! [`Tactic`] is a plain value, an interpreter runs it, and the deleted
//! driver comes back as one program among many ([`saturate_structural`]).
//!
//! Everything here is untrusted, and holding that line is the design. A
//! tactic mutates a graph through [`Derivation::push`] and nothing else, so
//! every step it takes goes through [`rules::apply`] — a buggy tactic
//! produces a refused step, never a wrong graph — and a run *is* a
//! derivation: replayable by [`rules::replay`], undoable by
//! [`Derivation::undo`], with nothing new to trust.
//!
//! Two primitives, matching the two ways a step comes to be:
//!
//! - [`Tactic::Fire`] — **found**, forward: a [`Query`] narrows to the box
//!   a rule is anchored at, [`rules::propose`] or
//!   [`rules::find_pinned`] produces the [`Match`](rules::Match), and
//!   payload blanks resolve by reading the bound box — the way
//!   `read_off` has always read them.
//! - [`Tactic::State`] — **stated**, either direction but above all
//!   backward: the matcher rightly declines every pattern that does not
//!   pin its own match, so those steps are *statements*, and a
//!   [`MatchSpec`] is the statement — every piece of it either a reading
//!   of the current graph or a genuine choice, the reader-split of
//!   [`Match::outputs`](rules::Match::outputs) said outright in
//!   [`SinkSel`] and never inferred.
//!
//! ## Addresses are queries, choices are stated
//!
//! A binding never crosses a rewrite. The interpreter re-runs every query
//! against the graph as it stands — after every single application, in
//! [`Pick::Each`] and [`Tactic::Repeat`] alike — so there is no stale
//! [`Match`] to hold and no incremental index to maintain; search is cheap
//! and untrusted, and it is spent freely. Where more than one answer
//! comes back, [`Pick`] says whose decision that is: the canonical first
//! (query order is part of [`query::eval`]'s meaning), every one until
//! dry, or exactly one on pain of [`TacticError::Ambiguous`]. Automorphic
//! duplicates — `dedup`'s two boxes swapped — are *counted*, not detected:
//! the deterministic order picks one and the derivation records which.
//!
//! ## A fatal failure leaves the graph standing
//!
//! On any error, [`run`] does not unwind committed work: the graph
//! reflects exactly the steps its derivation records, every one of which
//! passed [`rules::apply`], so a failed run leaves a well-formed graph to
//! look at — the last state of a rewrite in progress, with the derivation
//! as its provenance. The guarantee is structural: primitives fail before
//! mutating, and rollback exists only where a combinator's meaning demands
//! it — [`Tactic::Try`], and the alternatives of [`Tactic::First`].
//!
//! That rollback is **speculation on a clone**, not [`Derivation::undo`],
//! and the difference is worth recording. Undoing puts boxes *back*, and a
//! box put back is a new box with a new [`NodeId`] — a history that went
//! forward, undid, and went forward again records later matches against
//! ids that never exist when the derivation replays from the original
//! graph. So a speculative branch runs against a cloned graph, and on
//! success its steps replay onto the real one — which sits in exactly the
//! state the clone started from, and ids are handed out in order, so they
//! land identically. The derivation only ever grows, and stays what it is
//! for: a record that replays.

use std::collections::HashSet;
use std::fmt;

use super::query::{self, Bindings, Query, Var};
use super::rules::{self, Derivation, Direction, Law, Rule, Step};
use super::{Graph, NodeId, NodeKind, Sink, Source};

// ---- what a step says ------------------------------------------------------------

/// Which of a query's answers to spend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pick {
    /// The canonically-first answer. The workhorse.
    First,
    /// Keep firing — re-querying after every application — until the
    /// answer set is dry. At least one firing, or the step found nothing.
    Each,
    /// Exactly one answer, or [`TacticError::Ambiguous`] — for steps whose
    /// author is claiming uniqueness, automorphic duplicates included.
    Unique,
}

/// Where a fired step's rule comes from.
#[derive(Debug, Clone, PartialEq)]
pub enum RuleSpec {
    /// A payload stated outright, anchored by pinning pattern box `pin`
    /// to the box the query bound — [`rules::find_pinned`].
    Concrete { rule: Rule, anchor: Var, pin: usize },
    /// Payloads read off the bound box, law by law — the
    /// [`rules::propose`] path, and where a query's payload blanks
    /// resolve into the concrete rules the trusted side sees.
    ReadOff { laws: Vec<Law>, anchor: Var },
}

/// A source, described rather than named — resolved against the bindings
/// and the live graph at the moment the step fires.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SrcExpr {
    /// Output `port` of the bound node.
    PortOf(Var, usize),
    /// Whatever input `port` of the bound node currently reads.
    FeedOf(Var, usize),
    /// Boundary input `i` of the host.
    Input(usize),
}

/// One boundary output's readers, described. This is where the
/// reader-split — the one field of a [`Match`](rules::Match) that is a
/// choice rather than a reading — gets **stated**.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SinkSel {
    /// Every reader of the output's source that is an input port of the
    /// bound node.
    ReadersAt(Var),
    /// Input `port` of the bound node.
    PortOf(Var, usize),
    /// Boundary output `i` of the host.
    Output(usize),
    /// Every reader of the output's source not claimed by an earlier
    /// selector of this spec. At most one per spec, and stating it *is*
    /// the choice — nothing here is inferred.
    Rest,
}

/// The recipe for a stated [`Match`](rules::Match) against one side of one
/// rule. Resolution is pure reading; the result goes through
/// [`rules::apply`], so a wrong recipe is a refused step.
///
/// Deliberately weaker than the matcher: only *bound* nodes can stand in
/// the pattern's image, so a stated step whose pattern has boxes needs the
/// query to have bound them. What the matcher cannot read, the derivation
/// must literally say. An empty selector list says a boundary output
/// serves nobody.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchSpec {
    /// Image of the pattern's boxes. Empty for every box-less side.
    pub nodes: Vec<Var>,
    /// One per pattern boundary input.
    pub inputs: Vec<SrcExpr>,
    /// One selector list per pattern boundary output.
    pub outputs: Vec<Vec<SinkSel>>,
    /// One per pattern branch id: a bound fork or select, whose
    /// [`BranchId`](super::BranchId) is read off.
    pub branches: Vec<Var>,
}

/// What a focused tactic scopes its queries to.
#[derive(Debug, Clone, PartialEq)]
pub enum Region {
    /// The image of the immediately preceding step: the fresh boxes its
    /// recorded inverse names — data [`rules::apply`] produced, not data
    /// the tactic guessed. While the focus holds, each new step's image
    /// joins the region: the region is what the focus produced **plus
    /// what rewriting produced from it**.
    LastImage,
}

/// One strategy, as a value.
#[derive(Debug, Clone, PartialEq)]
pub enum Tactic {
    /// Found, forward: query, anchor, propose, pick, apply.
    Fire {
        at: Query,
        rule: RuleSpec,
        pick: Pick,
    },
    /// Stated, either direction: query, resolve the spec, apply.
    State {
        at: Query,
        rule: Rule,
        dir: Direction,
        with: MatchSpec,
        pick: Pick,
    },
    /// Each in order. A failure propagates and keeps the progress made —
    /// the graph stands at the last step that landed.
    Seq(Vec<Tactic>),
    /// The first alternative that succeeds; a failed alternative leaves
    /// no trace, by speculation on a clone.
    First(Vec<Tactic>),
    /// Failure becomes no progress, atomically. The way to say
    /// "optional".
    Try(Box<Tactic>),
    /// The body until it reports no progress, or fails having made none
    /// this round — which is how a saturation ends. `Some(n)` is fuel: a
    /// tripwire, not a budget, tripped loudly when an iteration advances
    /// past it. `None` is the author claiming termination.
    Repeat(Box<Tactic>, Option<usize>),
    /// Every query inside the body scoped to a region.
    Within(Region, Box<Tactic>),
}

/// What a run did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Progress {
    Advanced(usize),
    Unchanged,
}

impl Progress {
    fn steps(self) -> usize {
        match self {
            Progress::Advanced(n) => n,
            Progress::Unchanged => 0,
        }
    }

    fn of(n: usize) -> Progress {
        if n == 0 {
            Progress::Unchanged
        } else {
            Progress::Advanced(n)
        }
    }
}

/// Why a tactic stopped. A primitive that finds nothing **fails** — the
/// discipline [`crate::hant`] keeps, loudly, so a strategy that no longer
/// matches its graph says so — and [`Tactic::Try`] is the opt-out.
#[derive(Debug, Clone, PartialEq)]
pub enum TacticError {
    /// The query bound nothing, or nothing it bound offered a step.
    NothingFound { at: &'static str },
    /// More answers than the pick admits.
    Ambiguous { found: usize },
    /// [`rules::apply`] refused a step the tactic constructed — a tactic
    /// bug, carried with the refusal so it can be read.
    Refused(rules::Error),
    /// A spec named a variable the query does not bind.
    Unresolved { var: Var },
    /// A spec named a port a bound node does not have.
    OutOfRange { var: Var, port: usize },
    /// A spec read a branch off a box that is not an end of one.
    NoBranch { var: Var },
    /// More than one [`SinkSel::Rest`] in one spec.
    ManyRests,
    /// An iteration advanced past the fuel.
    OutOfFuel { after: usize },
}

impl fmt::Display for TacticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TacticError::NothingFound { at } => write!(f, "{} found nothing to do", at),
            TacticError::Ambiguous { found } => {
                write!(f, "one answer was claimed and {} were found", found)
            }
            TacticError::Refused(e) => write!(f, "a constructed step was refused: {}", e),
            TacticError::Unresolved { var } => write!(f, "{} is not bound by the query", var),
            TacticError::OutOfRange { var, port } => {
                write!(f, "{} has no port {}", var, port)
            }
            TacticError::NoBranch { var } => {
                write!(f, "{} is not an end of a branch", var)
            }
            TacticError::ManyRests => write!(f, "a spec says Rest twice"),
            TacticError::OutOfFuel { after } => {
                write!(f, "still advancing after {} iterations", after)
            }
        }
    }
}

impl std::error::Error for TacticError {}

// ---- running one -----------------------------------------------------------------

/// A tactic, run into a derivation. Every mutation lands through
/// [`Derivation::push`], so on `Ok` and `Err` alike the graph reflects
/// exactly the steps `deriv` records — checked, replayable, standing.
pub fn run(
    graph: &mut Graph,
    deriv: &mut Derivation,
    tactic: &Tactic,
) -> Result<Progress, TacticError> {
    Runner {
        graph,
        deriv,
        region: None,
    }
    .run(tactic)
}

struct Runner<'g> {
    graph: &'g mut Graph,
    deriv: &'g mut Derivation,
    /// The focus, when one is held: queries are scoped to it, and every
    /// landed step's image joins it.
    region: Option<HashSet<NodeId>>,
}

/// What a speculative run produced: the steps it landed on the clone, the
/// focus it ended holding, and what it reported.
struct Speculated {
    steps: Vec<Step>,
    region: Option<HashSet<NodeId>>,
    progress: Progress,
}

impl Runner<'_> {
    fn run(&mut self, tactic: &Tactic) -> Result<Progress, TacticError> {
        match tactic {
            Tactic::Fire { at, rule, pick } => self.fire(at, rule, *pick),
            Tactic::State {
                at,
                rule,
                dir,
                with,
                pick,
            } => self.state(at, rule, *dir, with, *pick),
            Tactic::Seq(steps) => {
                let mut total = 0;
                for step in steps {
                    total += self.run(step)?.steps();
                }
                Ok(Progress::of(total))
            }
            Tactic::First(alternatives) => {
                let mut last = TacticError::NothingFound { at: "first" };
                for alternative in alternatives {
                    match self.speculate(alternative) {
                        Ok(won) => return Ok(self.commit(won)),
                        Err(e) => last = e,
                    }
                }
                Err(last)
            }
            Tactic::Try(body) => match self.speculate(body) {
                Ok(won) => Ok(self.commit(won)),
                Err(_) => Ok(Progress::Unchanged),
            },
            Tactic::Repeat(body, fuel) => {
                let mut iterations = 0;
                let mut total = 0;
                loop {
                    let mark = self.deriv.len();
                    match self.run(body) {
                        Ok(Progress::Unchanged) => break,
                        Ok(Progress::Advanced(n)) => {
                            total += n;
                            iterations += 1;
                            if let Some(cap) = fuel
                                && iterations > *cap
                            {
                                return Err(TacticError::OutOfFuel { after: *cap });
                            }
                        }
                        // Dry: the body failed having landed nothing this
                        // round, which is how a saturation says it is done.
                        Err(_) if self.deriv.len() == mark => break,
                        // A failure with progress in the round is real, and
                        // the progress stands.
                        Err(e) => return Err(e),
                    }
                }
                Ok(Progress::of(total))
            }
            Tactic::Within(region, body) => {
                let focused = self.resolve_region(region);
                let held = self.region.take();
                self.region = Some(focused);
                let out = self.run(body);
                self.region = held;
                out
            }
        }
    }

    // -- the primitives --

    fn fire(&mut self, at: &Query, rule: &RuleSpec, pick: Pick) -> Result<Progress, TacticError> {
        match pick {
            Pick::First => {
                let step = self
                    .first_offer(at, rule)?
                    .ok_or(TacticError::NothingFound { at: "fire" })?;
                self.land(step)?;
                Ok(Progress::Advanced(1))
            }
            Pick::Unique => {
                let mut offers = self.offers(at, rule)?;
                match offers.len() {
                    0 => Err(TacticError::NothingFound { at: "fire" }),
                    1 => {
                        self.land(offers.pop().expect("one"))?;
                        Ok(Progress::Advanced(1))
                    }
                    found => Err(TacticError::Ambiguous { found }),
                }
            }
            Pick::Each => {
                let mut fired = 0;
                while let Some(step) = self.first_offer(at, rule)? {
                    self.land(step)?;
                    fired += 1;
                }
                if fired == 0 {
                    return Err(TacticError::NothingFound { at: "fire" });
                }
                Ok(Progress::Advanced(fired))
            }
        }
    }

    fn state(
        &mut self,
        at: &Query,
        rule: &Rule,
        dir: Direction,
        spec: &MatchSpec,
        pick: Pick,
    ) -> Result<Progress, TacticError> {
        match pick {
            Pick::First | Pick::Unique => {
                let bound = query::eval_in(self.graph, at, self.region.as_ref());
                if pick == Pick::Unique && bound.len() > 1 {
                    return Err(TacticError::Ambiguous { found: bound.len() });
                }
                let b = bound
                    .into_iter()
                    .next()
                    .ok_or(TacticError::NothingFound { at: "state" })?;
                let step = self.stated(rule, dir, spec, &b)?;
                self.land(step)?;
                Ok(Progress::Advanced(1))
            }
            Pick::Each => {
                let mut landed = 0;
                loop {
                    let bound = query::eval_in(self.graph, at, self.region.as_ref());
                    let Some(b) = bound.into_iter().next() else {
                        break;
                    };
                    let step = self.stated(rule, dir, spec, &b)?;
                    self.land(step)?;
                    landed += 1;
                }
                if landed == 0 {
                    return Err(TacticError::NothingFound { at: "state" });
                }
                Ok(Progress::Advanced(landed))
            }
        }
    }

    /// One binding's stated step: build the pattern side, resolve the
    /// spec against it.
    fn stated(
        &self,
        rule: &Rule,
        dir: Direction,
        spec: &MatchSpec,
        b: &Bindings,
    ) -> Result<Step, TacticError> {
        let (lhs, rhs) = rules::sides(rule).map_err(TacticError::Refused)?;
        let pattern = match dir {
            Direction::Forward => lhs,
            Direction::Backward => rhs,
        };
        let at = resolve(self.graph, &pattern, b, spec)?;
        Ok(Step {
            rule: rule.clone(),
            dir,
            at,
        })
    }

    /// Every step the query and rule spec offer, deduplicated, in
    /// canonical order: bindings as [`query::eval_in`] answers them, steps
    /// as the matcher finds them.
    fn offers(&self, at: &Query, rule: &RuleSpec) -> Result<Vec<Step>, TacticError> {
        let mut out: Vec<Step> = Vec::new();
        for b in query::eval_in(self.graph, at, self.region.as_ref()) {
            for step in self.offered(&b, rule)? {
                if !out.contains(&step) {
                    out.push(step);
                }
            }
        }
        Ok(out)
    }

    /// The canonically-first offer, without collecting the rest.
    fn first_offer(&self, at: &Query, rule: &RuleSpec) -> Result<Option<Step>, TacticError> {
        for b in query::eval_in(self.graph, at, self.region.as_ref()) {
            if let Some(step) = self.offered(&b, rule)?.into_iter().next() {
                return Ok(Some(step));
            }
        }
        Ok(None)
    }

    fn offered(&self, b: &Bindings, rule: &RuleSpec) -> Result<Vec<Step>, TacticError> {
        match rule {
            RuleSpec::ReadOff { laws, anchor } => {
                let id = b
                    .get(*anchor)
                    .ok_or(TacticError::Unresolved { var: *anchor })?;
                Ok(rules::propose(self.graph, laws, id))
            }
            RuleSpec::Concrete { rule, anchor, pin } => {
                let id = b
                    .get(*anchor)
                    .ok_or(TacticError::Unresolved { var: *anchor })?;
                let (lhs, _) = rules::sides(rule).map_err(TacticError::Refused)?;
                Ok(rules::find_pinned(self.graph, &lhs, *pin, id)
                    .into_iter()
                    .map(|at| Step {
                        rule: rule.clone(),
                        dir: Direction::Forward,
                        at,
                    })
                    .collect())
            }
        }
    }

    /// One step, through the one gate there is. On success the step's
    /// image joins the focus, read off the recorded inverse.
    fn land(&mut self, step: Step) -> Result<(), TacticError> {
        self.deriv
            .push(self.graph, step)
            .map_err(TacticError::Refused)?;
        if let Some(region) = &mut self.region {
            let back = self.deriv.latest_undo().expect("a step just landed");
            region.extend(back.at.nodes.iter().copied());
        }
        Ok(())
    }

    // -- speculation --

    /// The tactic, run against a clone. On success, the steps it landed —
    /// ready to replay onto the real graph, which sits in exactly the
    /// state the clone started from.
    fn speculate(&mut self, tactic: &Tactic) -> Result<Speculated, TacticError> {
        let mut graph = self.graph.clone();
        let mut deriv = self.deriv.clone();
        let mark = deriv.len();
        let mut sub = Runner {
            graph: &mut graph,
            deriv: &mut deriv,
            region: self.region.clone(),
        };
        let progress = sub.run(tactic)?;
        let region = sub.region;
        let steps = deriv.steps().skip(mark).cloned().collect();
        Ok(Speculated {
            steps,
            region,
            progress,
        })
    }

    /// A successful speculation, landed for real. Ids are handed out in
    /// order, so each step lands exactly where it landed on the clone —
    /// and the region the clone ended with carries over unchanged.
    fn commit(&mut self, won: Speculated) -> Progress {
        for step in won.steps {
            self.deriv
                .push(self.graph, step)
                .expect("a step that landed on the clone lands on what it was cloned from");
        }
        self.region = won.region;
        won.progress
    }

    fn resolve_region(&self, region: &Region) -> HashSet<NodeId> {
        match region {
            Region::LastImage => self
                .deriv
                .latest_undo()
                .map(|back| back.at.nodes.iter().copied().collect())
                .unwrap_or_default(),
        }
    }
}

// ---- resolving a stated match ----------------------------------------------------

/// [`MatchSpec`] × [`Bindings`] × the current graph → a concrete
/// [`Match`](rules::Match). Pure reading, and untrusted: the answer is
/// judged whole by [`rules::apply`], so a wrong resolution costs a refusal.
fn resolve(
    graph: &Graph,
    pattern: &Graph,
    b: &Bindings,
    spec: &MatchSpec,
) -> Result<rules::Match, TacticError> {
    if spec
        .outputs
        .iter()
        .flatten()
        .filter(|sel| matches!(sel, SinkSel::Rest))
        .count()
        > 1
    {
        return Err(TacticError::ManyRests);
    }
    let node_of = |v: Var| b.get(v).ok_or(TacticError::Unresolved { var: v });

    let mut nodes = Vec::with_capacity(spec.nodes.len());
    for &v in &spec.nodes {
        nodes.push(node_of(v)?);
    }

    let mut inputs = Vec::with_capacity(spec.inputs.len());
    for src in &spec.inputs {
        inputs.push(match *src {
            SrcExpr::PortOf(v, port) => Source::Port {
                node: node_of(v)?,
                port,
            },
            SrcExpr::FeedOf(v, port) => {
                let node = node_of(v)?;
                *graph
                    .sources(node)
                    .get(port)
                    .ok_or(TacticError::OutOfRange { var: v, port })?
            }
            SrcExpr::Input(i) => Source::Input(i),
        });
    }

    // The host source each pattern boundary output stands for, read the
    // way the checker will read it — which is what `ReadersAt` and `Rest`
    // select the readers of.
    let image = |src: Source| match src {
        Source::Input(i) => inputs.get(i).copied(),
        Source::Port { node, port } => nodes
            .get(node.index())
            .map(|&n| Source::Port { node: n, port }),
    };
    let mut outputs = Vec::with_capacity(spec.outputs.len());
    let mut claimed: Vec<Sink> = Vec::new();
    for (j, selectors) in spec.outputs.iter().enumerate() {
        let readers: Vec<Sink> = pattern
            .outputs()
            .get(j)
            .and_then(|&src| image(src))
            .map(|host| graph.sinks(host).to_vec())
            .unwrap_or_default();
        let mut list: Vec<Sink> = Vec::new();
        for selector in selectors {
            match *selector {
                SinkSel::PortOf(v, port) => list.push(Sink::Port {
                    node: node_of(v)?,
                    port,
                }),
                SinkSel::Output(i) => list.push(Sink::Output(i)),
                SinkSel::ReadersAt(v) => {
                    let node = node_of(v)?;
                    list.extend(
                        readers.iter().copied().filter(
                            |sink| matches!(sink, Sink::Port { node: n, .. } if *n == node),
                        ),
                    );
                }
                SinkSel::Rest => {
                    let rest: Vec<Sink> = readers
                        .iter()
                        .copied()
                        .filter(|sink| !claimed.contains(sink) && !list.contains(sink))
                        .collect();
                    list.extend(rest);
                }
            }
        }
        claimed.extend(list.iter().copied());
        outputs.push(list);
    }

    let mut branches = Vec::with_capacity(spec.branches.len());
    for &v in &spec.branches {
        let node = node_of(v)?;
        match graph.kind(node) {
            NodeKind::Fork { branch, .. } | NodeKind::Select { branch, .. } => {
                branches.push(*branch)
            }
            _ => return Err(TacticError::NoBranch { var: v }),
        }
    }

    Ok(rules::Match {
        nodes,
        inputs,
        outputs,
        branches,
    })
}

// ---- the library -----------------------------------------------------------------

/// The first proposal of any of these laws, at the canonically-first box
/// that offers one.
pub fn fire_first(laws: Vec<Law>) -> Tactic {
    Tactic::Fire {
        at: Query::new().is("n", query::NodePred::Any),
        rule: RuleSpec::ReadOff {
            laws,
            anchor: Var("n"),
        },
        pick: Pick::First,
    }
}

/// The deleted driver, as a program: the structural laws to fixpoint.
///
/// Terminates without fuel because every structural law strictly shrinks
/// the live box count — the argument the old worklist's doc made, now the
/// author's claim in the one place a strategy states its claims.
pub fn saturate_structural() -> Tactic {
    Tactic::Repeat(Box::new(fire_first(rules::structural())), None)
}

/// The whole table to fixpoint: the branch layer in its documented order,
/// the structural laws behind it, the value layer behind those — and
/// `view-value` behind everything, fired only when nothing else fires,
/// because spending a fork's views takes the specializing laws' anchor
/// with them.
///
/// This is the closest thing the tactic road has to a normalizer, and it
/// is still a strategy: those laws, in that order, everywhere they fire,
/// chosen here and replaceable by any proof that chooses differently.
pub fn decide() -> Tactic {
    Tactic::Repeat(
        Box::new(Tactic::First(vec![
            fire_first([rules::branching(), rules::structural(), rules::folding()].concat()),
            fire_first(vec![Law::ViewValue]),
        ])),
        None,
    )
}

/// The branch layer, spent to fixpoint with the structural cleanup it
/// needs.
///
/// The laws are tried in the order [`rules::branching`] documents —
/// `select-view` is what pulls a block out from behind a fork, and until
/// it has, most of the layer has nothing to match — with
/// [`rules::structural`] behind them to spend what a branch rewrite
/// leaves. What was advice in a doc comment is a program here.
pub fn branch_pass() -> Tactic {
    Tactic::Repeat(
        Box::new(fire_first(
            [rules::branching(), rules::structural()].concat(),
        )),
        None,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram2::meaning::{Meaning, boundary, eval_graph};
    use crate::diagram2::query::{KindPat, NodePred};
    use crate::diagram2::{build, rules::replay};
    use crate::term::{Context, Prim};
    use bytecode::{Value, assemble};

    fn built(body: &str) -> Graph {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        let mut terms = Context::new();
        let term = crate::term::lower(&mut terms, &library, idx).unwrap();
        let graph = build(&terms, term);
        graph.check().unwrap();
        graph
    }

    /// The two graphs are one program, judged with every operation left
    /// opaque — valid exactly for runs that spend only wiring laws.
    fn same_meaning(note: &str, a: &Graph, b: &Graph) {
        let mut m = Meaning::default();
        let inputs = boundary(&mut m, a.arity().inputs);
        assert_eq!(
            eval_graph(&mut m, a, &inputs),
            eval_graph(&mut m, b, &inputs),
            "{}: the run changed what the graph means:\n{}\n{}",
            note,
            a,
            b
        );
    }

    /// The coverage the deleted driver took with it, restored against the
    /// driver's replacement: meaning preserved across a run, the
    /// structural layer gone, idempotence, a whole graph at every end,
    /// the recorded derivation replaying to the same place, and the undo
    /// closing the valley.
    #[test]
    fn the_deleted_driver_is_a_program() {
        for body in [
            "swap swap",
            "dip { swap } swap dip { swap }",
            "push 9 pick 0",
            "pick 1 pick 1 equal drop 0",
            "branch { pick 0 drop 0 not } { not }",
        ] {
            let original = built(body);
            let mut graph = original.clone();
            let mut deriv = Derivation::default();
            run(&mut graph, &mut deriv, &saturate_structural())
                .unwrap_or_else(|e| panic!("{}: {}", body, e));
            graph
                .check()
                .unwrap_or_else(|e| panic!("{}: left a torn graph: {}", body, e));
            same_meaning(body, &original, &graph);
            for (_, kind) in graph.live() {
                assert!(
                    !kind.is_structural(),
                    "{}: the structural layer survived:\n{}",
                    body,
                    graph
                );
            }

            // Idempotence: a second run has nothing to do.
            let mut again = Derivation::default();
            assert_eq!(
                run(&mut graph, &mut again, &saturate_structural()),
                Ok(Progress::Unchanged),
                "{}: not a fixpoint",
                body
            );

            // The run IS its derivation: the recorded steps land the same
            // graph from the same start.
            let mut fresh = original.clone();
            let steps: Vec<Step> = deriv.steps().cloned().collect();
            replay(&mut fresh, &steps).unwrap_or_else(|e| panic!("{}: no replay: {}", body, e));
            assert_eq!(fresh, graph, "{}: the derivation lands elsewhere", body);

            // And the undo closes the valley.
            let mut back = graph.clone();
            deriv
                .undo(&mut back)
                .unwrap_or_else(|e| panic!("{}: no undo: {}", body, e));
            back.check().unwrap();
            assert_eq!(back.live_count(), original.live_count());
            same_meaning(body, &original, &back);
        }
    }

    #[test]
    fn the_two_spellings_of_swaps_settle_together() {
        let mut graph = built("swap swap");
        let mut deriv = Derivation::default();
        run(&mut graph, &mut deriv, &saturate_structural()).unwrap();
        assert_eq!(graph.live_count(), 0);
        assert_eq!(graph.outputs(), [Source::Input(0), Source::Input(1)]);
        assert_eq!(deriv.len(), 2);
    }

    /// The directed spelling: fold the literal condition — claiming there
    /// is exactly one — then clean up inside the image of that one step
    /// and nowhere else.
    #[test]
    fn a_literal_condition_keeps_its_arm() {
        let mut graph = built("push true branch { push 1 } { push 2 }");
        let mut deriv = Derivation::default();
        let tactic = Tactic::Seq(vec![
            Tactic::Fire {
                at: Query::new()
                    .is("sel", NodePred::Kind(KindPat::Select))
                    .is("lit", NodePred::Kind(KindPat::AnyPush))
                    .feeds("lit", 0, "sel", 0),
                rule: RuleSpec::ReadOff {
                    laws: vec![Law::SelectLiteral],
                    anchor: Var("sel"),
                },
                pick: Pick::Unique,
            },
            Tactic::Within(Region::LastImage, Box::new(saturate_structural())),
        ]);
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();
        // The arms take nothing, so there is no fork and each arm is a
        // *wire*: the two literals sit outside the window and survive the
        // fold. The image of the step is the fresh boxes it left — the
        // re-spent condition, which dead-node collects — and the focus is
        // exactly what makes the untaken `push 2`, dead but **outside**
        // the image, survive this pass. A focus that collected it would
        // not be a focus.
        assert_eq!(deriv.len(), 2, "the fold, and one dead-node inside it");
        assert_eq!(graph.live_count(), 2, "\n{}", graph);
        let dead = graph
            .live()
            .find(|(_, k)| *k == &NodeKind::Op(Prim::Push(Value::Int(2))))
            .map(|(id, _)| id)
            .expect("the untaken arm's literal is still there");
        assert!(
            graph
                .sinks(Source::Port {
                    node: dead,
                    port: 0
                })
                .is_empty()
        );

        // Unfocused, the cleanup reaches it.
        run(&mut graph, &mut deriv, &saturate_structural()).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 1, "\n{}", graph);
        let (kept, kind) = graph.live().next().unwrap();
        assert_eq!(kind, &NodeKind::Op(Prim::Push(Value::Int(1))));
        assert_eq!(
            graph.outputs(),
            [Source::Port {
                node: kept,
                port: 0
            }]
        );
    }

    /// A backward step, stated: the matcher rightly declines copy-elim's
    /// right side, and the spec is the vocabulary that states it — the
    /// reader-split said selector by selector, `Rest` included.
    #[test]
    fn a_stated_step_says_the_split() {
        let mut graph = Graph::empty(0);
        let nine = graph.add(NodeKind::Op(Prim::Push(Value::Int(9))), Vec::new());
        let not = graph.add(NodeKind::Op(Prim::Not), nine.clone());
        let negate = graph.add(NodeKind::Op(Prim::Negate), nine.clone());
        graph.close(vec![not[0], negate[0]]);
        graph.check().unwrap();

        let mut deriv = Derivation::default();
        let tactic = Tactic::State {
            at: Query::new()
                .is("nine", NodePred::Kind(KindPat::Push(Value::Int(9))))
                .is("n", NodePred::Kind(KindPat::Op(Some(Prim::Not))))
                .is("g", NodePred::Kind(KindPat::Op(Some(Prim::Negate))))
                .feeds("nine", 0, "n", 0)
                .feeds("nine", 0, "g", 0),
            rule: Rule::CopyElim { n: 1 },
            dir: Direction::Backward,
            with: MatchSpec {
                nodes: Vec::new(),
                inputs: vec![SrcExpr::FeedOf(Var("n"), 0)],
                // The split, stated: the `not` reads one leg, and whoever
                // is left — the `negate` — keeps the other.
                outputs: vec![vec![SinkSel::PortOf(Var("n"), 0)], vec![SinkSel::Rest]],
                branches: Vec::new(),
            },
            pick: Pick::Unique,
        };
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();

        let (copy, _) = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Copy(1)))
            .expect("the copy came back");
        let nine = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::Push(_))))
            .map(|(id, _)| id)
            .unwrap();
        let not = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::Not)))
            .map(|(id, _)| id)
            .unwrap();
        let negate = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::Negate)))
            .map(|(id, _)| id)
            .unwrap();
        assert_eq!(
            graph.sources(copy),
            [Source::Port {
                node: nine,
                port: 0
            }]
        );
        assert_eq!(
            graph.sources(not),
            [Source::Port {
                node: copy,
                port: 0
            }]
        );
        assert_eq!(
            graph.sources(negate),
            [Source::Port {
                node: copy,
                port: 1
            }]
        );

        // And the saturation takes the copy straight back out.
        run(&mut graph, &mut deriv, &saturate_structural()).unwrap();
        assert_eq!(graph.live_count(), 3);
    }

    /// A failed alternative leaves no trace, and — the point of cloning
    /// rather than undoing — what the run records still replays from the
    /// original graph, first try to last step.
    #[test]
    fn speculation_leaves_no_trace() {
        let original = built("swap swap");
        let mut graph = original.clone();
        let mut deriv = Derivation::default();
        // The first alternative advances one step and then dies looking
        // for a fork that is not there.
        let doomed = Tactic::Seq(vec![
            fire_first(vec![Law::SwapElim]),
            Tactic::Fire {
                at: Query::new().is("f", NodePred::Kind(KindPat::Fork)),
                rule: RuleSpec::ReadOff {
                    laws: vec![Law::DeadNode],
                    anchor: Var("f"),
                },
                pick: Pick::First,
            },
        ]);
        let tactic = Tactic::First(vec![doomed, saturate_structural()]);
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 0);
        assert_eq!(deriv.len(), 2, "only the winning alternative's steps");
        let mut fresh = original.clone();
        let steps: Vec<Step> = deriv.steps().cloned().collect();
        replay(&mut fresh, &steps).unwrap();
        assert_eq!(fresh, graph, "the record does not replay");
    }

    #[test]
    fn a_try_that_fails_is_a_quiet_nothing() {
        let mut graph = built("not");
        let mut deriv = Derivation::default();
        let hopeless = Tactic::Fire {
            at: Query::new().is("f", NodePred::Kind(KindPat::Fork)),
            rule: RuleSpec::ReadOff {
                laws: vec![Law::DeadNode],
                anchor: Var("f"),
            },
            pick: Pick::First,
        };
        assert!(matches!(
            run(&mut graph, &mut deriv, &hopeless),
            Err(TacticError::NothingFound { .. })
        ));
        assert_eq!(
            run(&mut graph, &mut deriv, &Tactic::Try(Box::new(hopeless))),
            Ok(Progress::Unchanged)
        );
        assert!(deriv.is_empty());
        assert_eq!(graph.live_count(), 1);
    }

    /// Fuel is a tripwire, and tripping it is a **fatal failure that
    /// leaves the graph standing**: every step that landed stays landed,
    /// the graph is whole, and the derivation says exactly what happened.
    #[test]
    fn out_of_fuel_leaves_the_graph_standing() {
        let original = built("swap swap");
        let mut graph = original.clone();
        let mut deriv = Derivation::default();
        let tactic = Tactic::Repeat(Box::new(fire_first(vec![Law::SwapElim])), Some(1));
        assert_eq!(
            run(&mut graph, &mut deriv, &tactic),
            Err(TacticError::OutOfFuel { after: 1 })
        );
        // Both steps landed before the wire tripped, and both stand.
        graph.check().unwrap();
        assert_eq!(deriv.len(), 2);
        let mut fresh = original.clone();
        let steps: Vec<Step> = deriv.steps().cloned().collect();
        replay(&mut fresh, &steps).unwrap();
        assert_eq!(fresh, graph);
    }

    /// `Unique` counts what `First` orders: two automorphic offers are
    /// two, on purpose — the deterministic order is the tie-break, and
    /// claiming uniqueness where there is symmetry is refused loudly.
    #[test]
    fn unique_counts_what_first_orders() {
        let graph = built("push 1 push 1 add");
        let ambiguous = Tactic::Fire {
            at: Query::new().is("p", NodePred::Kind(KindPat::AnyPush)),
            rule: RuleSpec::ReadOff {
                laws: vec![Law::Dedup],
                anchor: Var("p"),
            },
            pick: Pick::Unique,
        };
        let mut probe = graph.clone();
        let mut deriv = Derivation::default();
        assert_eq!(
            run(&mut probe, &mut deriv, &ambiguous),
            Err(TacticError::Ambiguous { found: 2 })
        );
        assert!(deriv.is_empty(), "a refused pick lands nothing");
        assert_eq!(probe, graph);

        let first = Tactic::Fire {
            at: Query::new().is("p", NodePred::Kind(KindPat::AnyPush)),
            rule: RuleSpec::ReadOff {
                laws: vec![Law::Dedup],
                anchor: Var("p"),
            },
            pick: Pick::First,
        };
        let mut probe = graph.clone();
        let mut deriv = Derivation::default();
        assert_eq!(
            run(&mut probe, &mut deriv, &first),
            Ok(Progress::Advanced(1))
        );
        probe.check().unwrap();
        assert_eq!(deriv.len(), 1);
    }

    /// A concrete payload, anchored by the box the query bound — the
    /// matcher pinned at the pattern box the tactic names rather than at
    /// whatever box the pattern begins with.
    #[test]
    fn a_concrete_rule_pins_where_the_query_points() {
        let mut graph = built("push 1 push 1 add");
        let mut deriv = Derivation::default();
        let tactic = Tactic::Fire {
            at: Query::new().is("p", NodePred::Kind(KindPat::Push(Value::Int(1)))),
            rule: RuleSpec::Concrete {
                rule: Rule::Dedup {
                    kind: NodeKind::Op(Prim::Push(Value::Int(1))),
                },
                anchor: Var("p"),
                pin: 1,
            },
            pick: Pick::First,
        };
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();
        assert_eq!(deriv.len(), 1);
        // One literal left, read twice.
        let pushes = graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Push(_))))
            .count();
        assert_eq!(pushes, 1, "\n{}", graph);
    }

    /// The branch layer, spent as a program: a branch whose arms answer
    /// alike dissolves to the one arm, and a literal condition keeps its
    /// own.
    #[test]
    fn the_branch_layer_is_a_pass() {
        // `branch { add } { add }` is fork-dedup, select-view,
        // select-same and then dead-node all the way down — wiring laws
        // throughout, so the opaque oracle can hold the run to meaning.
        let original = built("branch { add } { add }");
        let mut graph = original.clone();
        let mut deriv = Derivation::default();
        run(&mut graph, &mut deriv, &branch_pass()).unwrap();
        graph.check().unwrap();
        same_meaning("branch { add } { add }", &original, &graph);
        assert_eq!(graph.live_count(), 1, "\n{}", graph);
        let (_, kind) = graph.live().next().unwrap();
        assert_eq!(kind, &NodeKind::Op(Prim::Add));

        // And β: the literal keeps its arm. Not oracle-judgeable — the
        // whole content is what `truthy` computes — so the claim here is
        // the shape.
        let mut graph = built("push true branch { push 1 } { push 2 }");
        let mut deriv = Derivation::default();
        run(&mut graph, &mut deriv, &branch_pass()).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 1, "\n{}", graph);
        let (_, kind) = graph.live().next().unwrap();
        assert_eq!(kind, &NodeKind::Op(Prim::Push(Value::Int(1))));
    }
}
