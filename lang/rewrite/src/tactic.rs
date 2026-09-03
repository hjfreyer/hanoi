//! The driver, as data: tactics over the table in [`rules`] and the
//! queries in [`query`], run into a [`Derivation`].
//!
//! No driver lives in [`rules`], and none should: *which* laws, *where*,
//! and *in what order* is a strategy, and a strategy belongs to whoever
//! is proving something. This module is where one is **written**: a
//! [`Tactic`] is a plain value, an interpreter runs it, and a driver is
//! one program among many ([`decide`]).
//!
//! Everything here is untrusted, and holding that line is the design. A
//! tactic mutates a graph through [`Derivation::push`] and nothing else, so
//! every step it takes goes through [`rules::apply`] — a buggy tactic
//! produces a refused step, never a wrong graph — and a run *is* a
//! derivation: replayable by [`rules::replay`], undoable by
//! [`Derivation::undo`], with nothing new to trust.
//!
//! Three primitives, matching the ways a step comes to be:
//!
//! - [`Tactic::Fire`] — **found**, forward: a [`Query`] narrows to the box
//!   a rule is anchored at, [`rules::propose`] or
//!   [`find_pinned`] produces the [`Match`], and
//!   payload blanks resolve by reading the bound box — the way
//!   `read_off` has always read them.
//! - [`Tactic::At`] — **found at a named box**, either direction: the
//!   address is a [`Prefix`] of one copied off a residual listing, and the
//!   search is [`rules::instances`] × [`find_over`]
//!   over every pattern box, so a match counts when it holds that box
//!   anywhere — except for the two laws whose payload is a *region*
//!   ([`Law::carries_a_region`]), where a match holding the box in the
//!   region it carries is another branch's equation rather than this
//!   one's, so the named box is where the law anchors and nowhere else.
//!   The
//!   one address that is a name rather than a description, and the one a
//!   person writes by pointing at a report.
//! - [`Tactic::State`] — **stated**, either direction but above all
//!   backward: the matcher rightly declines every pattern that does not
//!   pin its own match, so those steps are *statements*, and a
//!   [`MatchSpec`] is the statement — which boxes stand in the pattern's
//!   image, and which wires its boundary inputs mean, every piece a
//!   reading of the current graph.
//!
//! ## Addresses are queries, choices are stated
//!
//! A binding does not cross a rewrite. The interpreter re-runs every query
//! against the graph as it stands — after every single application, in
//! [`Pick::Each`] and [`Tactic::Repeat`] alike — so there is no stale
//! [`Match`] to hold and no incremental index to maintain; search is cheap
//! and untrusted, and it is spent freely. Where more than one answer
//! comes back, [`Pick`] says whose decision that is: the canonical first
//! (query order is part of [`query::eval`]'s meaning), every one until
//! dry, or exactly one on pain of [`TacticError::Ambiguous`]. Automorphic
//! duplicates — a symmetric pattern's two boxes swapped — are *counted*,
//! not detected:
//! the deterministic order picks one and the derivation records which.
//!
//! [`Tactic::At`] is the exception that keeps the rule honest. It holds a
//! name — as much of an [`Address`] as told that box from the others when
//! the report was printed — and holds it across no rewrite: it is looked
//! up live at every entry, re-searched between firings like everything
//! else, and it fails by name the moment the box it points at computes
//! something else ([`TacticError::NoSuchBox`]) or the prefix has come to
//! mean two boxes ([`TacticError::ManyBoxes`]). What licenses it is the
//! residual listing, which is keyed by address precisely so that a next
//! step can name what the report named.
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
//! box put back is a new box with a new [`NodeId`] — so under a record
//! that names boxes by id, a history that went forward, undid, and went
//! forward again records later matches against ids that never exist when
//! the derivation replays from the original graph. So a speculative branch runs against a cloned graph, and on
//! success its steps replay onto the real one — which sits in exactly the
//! state the clone started from, and ids are handed out in order, so they
//! land identically. The derivation only ever grows, and stays what it is
//! for: a record that replays.

use std::collections::HashSet;
use std::fmt;

use crate::kernel::graph::{
    Address, Direction, Graph, Lifted, Match, Named, NodeId, NodeKind, Prefix, Sink, Source,
    find_over, find_pinned, lift,
};
use crate::kernel::rules::{self, Derivation, Law, Rule, Step};
use crate::query::{self, Bindings, Query, Var};

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
    /// to the box the query bound — [`find_pinned`].
    Concrete { rule: Rule, anchor: Var, pin: usize },
    /// Payloads read off the bound box, law by law — the
    /// [`rules::propose`] path, and where a query's payload blanks
    /// resolve into the concrete rules the trusted side sees.
    ReadOff { laws: Vec<Law>, anchor: Var },
    /// [`Law::SelectHoist`] with the body computed **here**: everything
    /// downstream of the bound select's answers except another select
    /// ([`hoistable`]).
    ///
    /// The payload a `select-hoist` carries is a region, and how much of
    /// one a branch should swallow is a strategy's decision rather than
    /// the table's. [`rules::propose`] reads the whole cone, branches
    /// and all, which is what a proof asking for one firing wants. A
    /// decision tree wants the other reading — every branch it meets
    /// left standing, so that hoisting sorts the selects to the end
    /// instead of copying them — and this is where it is said.
    ///
    /// A **stated** step, for the reason every stated step is one: the
    /// body was lifted off particular host boxes, and which boxes those
    /// were is a reading nothing in the pattern records. The match says
    /// it outright.
    Hoist { anchor: Var },
}

/// A source, described or named — resolved against the bindings and the
/// live graph at the moment the step fires.
#[derive(Debug, Clone, PartialEq)]
pub enum SrcExpr {
    /// Output `port` of the bound node.
    PortOf(Var, usize),
    /// Whatever input `port` of the bound node currently reads.
    FeedOf(Var, usize),
    /// Boundary input `i` of the host.
    Input(usize),
    /// Output `port` of the box the written address names — the wire
    /// spelling of [`Tactic::At`]'s box name, under the same discipline:
    /// looked up live at every firing rather than held, failing by name
    /// the moment nothing answers to it or two boxes do.
    Addressed(Prefix, usize),
}

/// A wire, written the way a listing prints one: `in2` is boundary input
/// 2, `#nk` is output 0 of the box that address names, and `#nk.1` a later
/// port.
///
/// [`SrcExpr`] says the same things and more, and cannot be used here: its
/// other two forms read a [`Bindings`], and an [`Tactic::At`] has no query
/// to have bound anything. What is left is exactly what a person can write
/// off a report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Wire {
    /// Boundary input `i` of the side.
    Input(usize),
    /// Output `port` of the box the written address names, under
    /// [`Tactic::At`]'s discipline: looked up live rather than held.
    Port(Prefix, usize),
}

impl fmt::Display for Wire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Wire::Input(i) => write!(f, "in{}", i),
            // A `Prefix` writes its own `#`, the way a listing does.
            Wire::Port(at, 0) => write!(f, "{}", at),
            Wire::Port(at, port) => write!(f, "{}.{}", at, port),
        }
    }
}

/// What an [`Tactic::At`] is aimed at: a box, or a set of them read off a
/// wire.
///
/// One box was the whole of it while a `select` carried every answer of
/// its branch. It carries one now, so the branch a wire decides is `n`
/// boxes — peers, none of them the branch on its own — and a proof that
/// wants to spend a row on *the branch* has `n` addresses to write and no
/// way to know `n` without reading the report. [`Aim::SelectsOn`] is the
/// name of the set instead, which is the same thing the listing draws one
/// bracket around.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Aim {
    /// The one box the written address names.
    Box(Prefix),
    /// Every live `select` that turns on this wire — its condition, port
    /// 0, and never a block. Read **literally**: a branch nested inside
    /// another that retests the same wire turns on it too, and is in.
    /// (The listing's bracket is the outermost peers, which is a
    /// different question and a sharper address.)
    SelectsOn(Wire),
}

impl fmt::Display for Aim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Aim::Box(at) => write!(f, "{}", at),
            Aim::SelectsOn(wire) => write!(f, "selects-on({})", wire),
        }
    }
}

/// A reader of a wire, named the way a listing prints one: a box by
/// address, or a boundary output by index. What a [`Readers`] clause is
/// written in, under [`Tactic::At`]'s discipline — looked up live at
/// every firing rather than held.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reader {
    /// The box the written address names — every port of it that reads a
    /// wire the stated law leaves.
    Box(Prefix),
    /// Boundary output `i` of the side.
    Output(usize),
}

impl fmt::Display for Reader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reader::Box(at) => write!(f, "{}", at),
            Reader::Output(i) => write!(f, "out{}", i),
        }
    }
}

/// Which of a wire's readers a step is for: the [`Match`]'s selection,
/// spelled in names rather than sinks.
///
/// Resolved against the live side at the moment the step is stated —
/// `Except` takes the complement of what the wire's readers are *then*,
/// so the recorded match carries a concrete selection either way, and a
/// reader a later step creates is not retroactively covered (the same
/// statement-time semantics the η a `cases` spends has). Absent, the step is
/// what it always was: every reader follows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Readers {
    /// These readers come to read through the law's window; every other
    /// reader keeps the wire it has.
    For(Vec<Reader>),
    /// Every reader follows except these, which keep the wire they have.
    Except(Vec<Reader>),
}

/// The recipe for a stated [`Match`] against one side of one
/// rule. Resolution is pure reading; the result goes through
/// [`rules::apply`], so a wrong recipe is a refused step.
///
/// Deliberately weaker than the matcher: only *bound* nodes can stand in
/// the pattern's image, so a stated step whose pattern has boxes needs the
/// query to have bound them. What the matcher cannot read, the derivation
/// must literally say. Nothing about outputs is said here: the
/// reader-split, where a proof wants one, is a [`Readers`] clause beside
/// the spec rather than anything the matcher could answer.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchSpec {
    /// Image of the pattern's boxes. Empty for every box-less side.
    pub nodes: Vec<Var>,
    /// One per pattern boundary input.
    pub inputs: Vec<SrcExpr>,
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
    /// One side of a branch: the boxes of the named arm — computed by
    /// [`arm_nodes`], fresh at every entry — plus the `select` itself,
    /// since the branch layer's laws are read off it and a focus that
    /// excluded it could never specialize or discharge.
    ///
    /// The branch is named by **what it tests**, not by a box: a rewrite
    /// that narrows a select puts down a new box with a new [`NodeId`],
    /// and the wire it turns on is what survives that. A condition
    /// nothing branches on any more resolves to the empty region, which
    /// binds nothing.
    ///
    /// Runtime data, and no surface syntax spells it today: the source is
    /// only known once a split has landed, so whoever names one reads it
    /// off what [`Derivation::latest_undo`] recorded. A `cases` used to
    /// be its one caller, scoping a case's rewrites to the side of the
    /// branch it had just made; it is a splitter now and hands each case
    /// the block as a goal of its own instead, which needs no region.
    /// This stays as what it always was here — a capability the data
    /// model has before the surface does, kept because reasoning inside
    /// one arm of a branch a goal already holds is a thing a tactic will
    /// want to say.
    Arm { cond: Source, side: bool },
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
    /// Found at a **named box**: the one address that is a name rather
    /// than a description, and the one a residual listing hands you
    /// ready-made.
    ///
    /// Everything else here addresses by [`Query`], because a description
    /// goes on meaning something after a rewrite has run. This is the
    /// deliberate exception, and it earns its place from the other end: a
    /// stuck goal prints one line per box, keyed by [`Address`], and the
    /// whole point of that listing is that *a next step names the boxes it
    /// names*. Without this variant there is no way to say back what the
    /// report just said.
    ///
    /// The name is written as a [`Prefix`] — as much of the address as
    /// tells that box from the others, which is what the listing
    /// emphasises — and is resolved against the side's live boxes at every
    /// entry ([`Graph::lookup`]). An address is a fact about what the box
    /// computes rather than about the graph holding it, so it goes on
    /// meaning that box across the steps that leave it alone and across
    /// both sides of the goal; what it does not survive is a rewrite
    /// under it, because a value made of different values is a different
    /// value. What it buys is precision nothing else offers — not "the
    /// first `fold` that fires", but *that one*.
    ///
    /// The search is the mirror of [`rules::propose`]'s. Every equation
    /// the law comes to in this graph ([`rules::instances`]) is looked
    /// for with each of its pattern boxes pinned in turn to `node`
    /// ([`find_over`]), so a match counts when it holds the box
    /// **anywhere**, not only where the pattern happens to anchor. `dir`
    /// says which side of the equation is the pattern: `Forward` matches
    /// the left and leaves the right, `Backward` the other way round —
    /// and backward finds something only where the law's right-hand side
    /// names enough boxes to pin itself, which most of the table's do
    /// not. Where it finds nothing it says so, loudly, naming the box and
    /// the law.
    At {
        at: Aim,
        law: Law,
        dir: Direction,
        pick: Pick,
        /// Which readers of what the law leaves follow it — `None` is all
        /// of them, which is what a substitution always meant.
        readers: Option<Readers>,
    },
    /// Stated, either direction: query, resolve the spec, apply.
    State {
        at: Query,
        rule: Rule,
        dir: Direction,
        with: MatchSpec,
        pick: Pick,
        /// Which readers of what the rule leaves follow it — `None` is
        /// all of them.
        readers: Option<Readers>,
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
    /// An address — [`Tactic::At`]'s box, or a stated wire's — that no
    /// live box of this side answers to: a name read off a listing from
    /// before the step in front of it changed what that box computes.
    NoSuchBox { at: Prefix },
    /// An address several boxes answer to, with the ones it could have
    /// meant — lengthen it.
    ManyBoxes { at: Prefix, found: Vec<Address> },
    /// [`Aim::SelectsOn`] named a wire no live `select` turns on. Said
    /// apart from an address nothing answers to: the wire is there, and
    /// nothing branches on it.
    NoSelectsOn { wire: Wire },
    /// [`Tactic::At`] found the box, and no match of that law in that
    /// direction holds it.
    NoMatchAt {
        at: Address,
        law: Law,
        dir: Direction,
    },
    /// A spec named a variable the query does not bind.
    Unresolved { var: Var },
    /// A spec named a port a bound node does not have.
    OutOfRange { var: Var, port: usize },
    /// A stated wire named a port its box does not have.
    NoSuchPort { at: Prefix, port: usize },
    /// A `for(...)`/`except(...)` output index past the boundary.
    NoSuchOutput { port: usize },
    /// A `for(...)`/`except(...)` reader that reads no wire the stated
    /// law leaves: the selection is about those wires, and this reader is
    /// off all of them.
    ReaderOffWire { reader: Reader },
    /// An `except(...)` that excepted every reader there was. The step
    /// would re-point nobody, and a step that finds nothing to do fails
    /// loudly rather than becoming a no-op.
    NobodyLeft,
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
            TacticError::NoSuchBox { at } => {
                write!(f, "{} is not a live box of this side", at)
            }
            TacticError::ManyBoxes { at, found } => write!(
                f,
                "{} is {} boxes of this side: {}",
                at,
                found.len(),
                found
                    .iter()
                    .map(Address::to_string)
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            TacticError::NoSelectsOn { wire } => {
                write!(f, "no live branch of this side turns on {}", wire)
            }
            TacticError::NoMatchAt { at, law, dir } => write!(
                f,
                "no {} `{}` match holds {}",
                match dir {
                    Direction::Forward => "forward",
                    Direction::Backward => "backward",
                },
                law,
                at
            ),
            TacticError::Refused(e) => write!(f, "a constructed step was refused: {}", e),
            TacticError::Unresolved { var } => write!(f, "{} is not bound by the query", var),
            TacticError::OutOfRange { var, port } => {
                write!(f, "{} has no port {}", var, port)
            }
            TacticError::NoSuchPort { at, port } => {
                write!(f, "{} has no output port {}", at, port)
            }
            TacticError::NoSuchOutput { port } => {
                write!(f, "the boundary has no output {}", port)
            }
            TacticError::ReaderOffWire { reader } => {
                write!(f, "{} reads no wire this law leaves", reader)
            }
            TacticError::NobodyLeft => {
                write!(
                    f,
                    "every reader was excepted, and the step would state nothing"
                )
            }
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
            Tactic::At {
                at,
                law,
                dir,
                pick,
                readers,
            } => match at {
                Aim::Box(at) => {
                    let node = self.named(at)?;
                    self.fire_at(node, *law, *dir, *pick, readers.as_ref())
                        .map(Progress::of)
                }
                Aim::SelectsOn(wire) => {
                    self.fire_at_each(wire, *law, *dir, *pick, readers.as_ref())
                }
            },
            Tactic::State {
                at,
                rule,
                dir,
                with,
                pick,
                readers,
            } => self.state(at, rule, *dir, with, *pick, readers.as_ref()),
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

    /// [`Tactic::At`]: the named box, that law, that direction.
    ///
    /// The shape is [`fire`](Runner::fire)'s, and it re-searches between
    /// firings for the same reason — a [`Match`](rules::Match) never
    /// crosses an [`apply`](rules::apply). The address does not need
    /// re-resolving, being an id already; what needs re-asking is which
    /// matches still hold it.
    /// The live box an address names.
    ///
    /// The three answers are three different mistakes, said apart: an
    /// address nothing answers to is a proof reading a listing from before
    /// the step in front of it changed what that box computes, and that is
    /// worth its own sentence; an address several boxes answer to wants
    /// lengthening; and only the third is a box.
    fn named(&self, at: &Prefix) -> Result<NodeId, TacticError> {
        match self.graph.lookup(at) {
            Named::One(node) => Ok(node),
            Named::Nothing => Err(TacticError::NoSuchBox { at: at.clone() }),
            Named::Many(found) => Err(TacticError::ManyBoxes {
                at: at.clone(),
                found,
            }),
        }
    }

    /// The wire a [`Wire`] names, resolved against the live side.
    fn wire(&self, wire: &Wire) -> Result<Source, TacticError> {
        match wire {
            Wire::Input(i) => Ok(Source::Input(*i)),
            Wire::Port(at, port) => Ok(Source::Port {
                node: self.named(at)?,
                port: *port,
            }),
        }
    }

    /// [`Aim::SelectsOn`]: that law, that direction, once at **every**
    /// `select` the wire turns on.
    ///
    /// The set is read once, at entry, and kept as **addresses** rather
    /// than ids — the discipline every other address here is under, and
    /// here it matters twice over. A firing rebuilds boxes, so an
    /// id would go stale; and `select-hoist` puts down fresh selects on the
    /// very same condition, so re-reading the set between firings would
    /// find the step's own answers and never finish. What the step means is
    /// the branch as it stood when the step was reached.
    ///
    /// A member that is gone by its turn is skipped and not mourned: a
    /// firing at one answer may take another with it, and a step that
    /// insisted on the count would be brittle for nothing. A member still
    /// standing that the law cannot fire at is the loud case — that is
    /// [`TacticError::NoMatchAt`], naming the box.
    fn fire_at_each(
        &mut self,
        wire: &Wire,
        law: Law,
        dir: Direction,
        pick: Pick,
        readers: Option<&Readers>,
    ) -> Result<Progress, TacticError> {
        let cond = self.wire(wire)?;
        let aimed: Vec<Address> = self
            .graph
            .live()
            .filter(|(id, kind)| {
                matches!(kind, NodeKind::Select) && self.graph.sources(*id).first() == Some(&cond)
            })
            .map(|(id, _)| self.graph.address(id))
            .collect();
        if aimed.is_empty() {
            return Err(TacticError::NoSelectsOn { wire: wire.clone() });
        }
        let mut total = 0;
        for address in aimed {
            let prefix = Prefix::parse(&address.to_string()).expect("an address is a prefix");
            let node = match self.graph.lookup(&prefix) {
                Named::One(node) => node,
                // Taken by an earlier firing, which is allowed.
                Named::Nothing => continue,
                Named::Many(found) => {
                    return Err(TacticError::ManyBoxes { at: prefix, found });
                }
            };
            total += self.fire_at(node, law, dir, pick, readers)?;
        }
        Ok(Progress::of(total))
    }

    fn fire_at(
        &mut self,
        node: NodeId,
        law: Law,
        dir: Direction,
        pick: Pick,
        readers: Option<&Readers>,
    ) -> Result<usize, TacticError> {
        let address = self.graph.address(node);
        let missing = || TacticError::NoMatchAt {
            at: address,
            law,
            dir,
        };
        match pick {
            Pick::First => {
                let step = self.at_offers(node, law, dir).into_iter().next();
                let step = self.select(step.ok_or_else(missing)?, readers)?;
                self.land(step)?;
                Ok(1)
            }
            Pick::Unique => {
                let mut offers = self.at_offers(node, law, dir);
                match offers.len() {
                    0 => Err(missing()),
                    1 => {
                        let step = self.select(offers.pop().expect("one"), readers)?;
                        self.land(step)?;
                        Ok(1)
                    }
                    found => Err(TacticError::Ambiguous { found }),
                }
            }
            Pick::Each => {
                let mut fired = 0;
                // A firing may delete the box it was aimed at, and then
                // there is nothing left to hold anything — which is one
                // way this ends.
                while self.graph.is_live(node)
                    && let Some(step) = self.at_offers(node, law, dir).into_iter().next()
                {
                    let step = self.select(step, readers)?;
                    self.land(step)?;
                    fired += 1;
                }
                if fired == 0 {
                    return Err(missing());
                }
                Ok(fired)
            }
        }
    }

    /// A step, held to a stated reader selection.
    ///
    /// This is where a `for(...)`/`except(...)` clause becomes the
    /// [`Match`]'s `sel`: the wires the selection is about are what the
    /// step's pattern side *leaves*, read off the match, and each named
    /// reader resolves to its sinks on those wires against the live side —
    /// so an `except` is a concrete complement taken now, and the
    /// recorded step replays without re-asking. Untrusted like every
    /// resolution here: the selection travels inside the match, and
    /// [`rules::apply`] holds it reader by reader.
    fn select(&self, step: Step, readers: Option<&Readers>) -> Result<Step, TacticError> {
        let Some(readers) = readers else {
            return Ok(step);
        };
        let pair = rules::sides(&step.rule).map_err(TacticError::Refused)?;
        let pattern = pair.pattern(step.dir);
        let image = |src: Source| match src {
            Source::Input(i) => step.at.inputs[i],
            Source::Port { node, port } => Source::Port {
                node: step.at.nodes[node.index()],
                port,
            },
        };
        let keys: Vec<Source> = pattern.outputs().iter().map(|&src| image(src)).collect();

        // A named reader, as its sinks on the step's wires — every port of
        // a box that reads one of them, or the one boundary output. A
        // reader off all of the wires is a name that states nothing, said
        // loudly.
        let resolve = |reader: &Reader| -> Result<Vec<Sink>, TacticError> {
            let sinks: Vec<Sink> = match reader {
                Reader::Box(at) => {
                    let node = self.named(at)?;
                    self.graph
                        .sources(node)
                        .iter()
                        .enumerate()
                        .filter(|(_, src)| keys.contains(src))
                        .map(|(port, _)| Sink::Port { node, port })
                        .collect()
                }
                Reader::Output(i) => {
                    let read = self
                        .graph
                        .outputs()
                        .get(*i)
                        .ok_or(TacticError::NoSuchOutput { port: *i })?;
                    keys.contains(read)
                        .then_some(Sink::Output(*i))
                        .into_iter()
                        .collect()
                }
            };
            if sinks.is_empty() {
                return Err(TacticError::ReaderOffWire {
                    reader: reader.clone(),
                });
            }
            Ok(sinks)
        };
        let reads = |sink: Sink| match sink {
            Sink::Output(i) => self.graph.outputs()[i],
            Sink::Port { node, port } => self.graph.sources(node)[port],
        };

        let sel: Vec<Vec<Sink>> = match readers {
            Readers::For(list) => {
                let mut per: Vec<Vec<Sink>> = vec![Vec::new(); keys.len()];
                for reader in list {
                    for sink in resolve(reader)? {
                        for (j, &key) in keys.iter().enumerate() {
                            if reads(sink) == key && !per[j].contains(&sink) {
                                per[j].push(sink);
                            }
                        }
                    }
                }
                per
            }
            Readers::Except(list) => {
                let mut kept: HashSet<Sink> = HashSet::new();
                for reader in list {
                    kept.extend(resolve(reader)?);
                }
                let per: Vec<Vec<Sink>> = keys
                    .iter()
                    .map(|&key| {
                        self.graph
                            .sinks(key)
                            .into_iter()
                            .filter(|sink| !kept.contains(sink))
                            .collect()
                    })
                    .collect();
                if per.iter().all(Vec::is_empty) {
                    return Err(TacticError::NobodyLeft);
                }
                per
            }
        };
        Ok(Step {
            at: Match {
                sel: Some(sel),
                ..step.at
            },
            ..step
        })
    }

    /// Every step of `law`, in direction `dir`, whose match holds `node`.
    ///
    /// Two sweeps, and the second is the point. [`rules::instances`]
    /// answers which equations the law comes to in this graph;
    /// [`rules::find_pinned`] is then asked once per pattern box, pinning
    /// *that* box to `node`, so the answers are the matches holding the
    /// named box anywhere in their image rather than only at the box a
    /// pattern happens to anchor on. A pattern that does not pin its own
    /// match answers nothing, for every pin — which is how the backward
    /// direction declines the rows it cannot search for.
    ///
    /// Except for the two laws that carry a **region**
    /// ([`Law::carries_a_region`]), which are anchored instead: see
    /// below.
    ///
    /// Deduplicated and left in the order the sweeps found it: instances
    /// in live-box order, pins in pattern order, matches in the matcher's
    /// own. Untrusted like every other search here — [`rules::apply`]
    /// judges whatever this hands it.
    fn at_offers(&self, node: NodeId, law: Law, dir: Direction) -> Vec<Step> {
        // A focus scopes anchors, and this is an anchor: a box outside the
        // region is not this tactic's to name.
        if self.region.as_ref().is_some_and(|r| !r.contains(&node)) {
            return Vec::new();
        }
        // A region-carrying law is anchored, and this is where that is
        // spent: [`rules::propose`] reads the payload off the box named
        // and pins the pattern where the law itself anchors, which for
        // `select-hoist` is the branch that moves.
        //
        // The sweep below would answer with more than that, and the more
        // is not other readings of the same equation — it is one equation
        // per *other* branch whose cone happens to hold this box, matched
        // on a payload box rather than on anything the law is about.
        // `at(#a-late-branch, select-hoist)` would then hoist the
        // earliest branch above it, which is not the branch anybody wrote
        // that address for.
        //
        // The one other thing it drops is a body some *other* branch's
        // cone spelled that is a piece of this one — a partial hoist,
        // reachable only by the accident of another branch in the same
        // graph having exactly that sub-cone. How much of a region a
        // branch should swallow is a strategy's decision (see
        // [`RuleSpec::Hoist`]), and the two readings a strategy can ask
        // for are the whole cone, which is this, and the cone without
        // its branches, which is `hoistable`. Neither is a leftover of
        // somebody else's window.
        //
        // It would also pay for them. A cone-sized pattern is pinned once
        // per box, every pin whose kind is the named box's re-sweeping
        // the live graph for the branch the pattern begins with, and the
        // whole of it once per branch in the program: measured at 329ms
        // against `propose`'s 55µs on a 208-box decision tree, and
        // growing about cubically where `propose` is flat.
        //
        // Backward is left to the sweep. `instances` reads a region off a
        // box's cone and never off the answer side, so no payload for a
        // backward step is found this way in the first place, and
        // narrowing a search that answers nothing would only be claiming
        // something about it that has not been established.
        if law.carries_a_region() && dir == Direction::Forward {
            return rules::propose(self.graph, &[law], node);
        }
        let mut out: Vec<Step> = Vec::new();
        for rule in rules::instances(self.graph, law) {
            let Ok(pair) = rules::sides(&rule) else {
                continue;
            };
            for at in find_over(self.graph, pair.pattern(dir), node) {
                let step = Step {
                    rule: rule.clone(),
                    dir,
                    at,
                };
                if !out.contains(&step) {
                    out.push(step);
                }
            }
        }
        out
    }

    fn state(
        &mut self,
        at: &Query,
        rule: &Rule,
        dir: Direction,
        spec: &MatchSpec,
        pick: Pick,
        readers: Option<&Readers>,
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
                let step = self.select(self.stated(rule, dir, spec, &b)?, readers)?;
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
                    let step = self.select(self.stated(rule, dir, spec, &b)?, readers)?;
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

    /// One binding's stated step: hold the payload to stating an equation,
    /// then resolve the spec.
    fn stated(
        &self,
        rule: &Rule,
        dir: Direction,
        spec: &MatchSpec,
        b: &Bindings,
    ) -> Result<Step, TacticError> {
        rules::sides(rule).map_err(TacticError::Refused)?;
        let at = resolve(self.graph, b, spec)?;
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
            RuleSpec::Hoist { anchor } => {
                let id = b
                    .get(*anchor)
                    .ok_or(TacticError::Unresolved { var: *anchor })?;
                if !matches!(self.graph.kind(id), NodeKind::Select) {
                    return Ok(Vec::new());
                }
                let Some(body) = hoistable(self.graph, id) else {
                    return Ok(Vec::new());
                };
                // Stated rather than searched for, and it has to be:
                // the body was lifted off these very boxes, and a
                // search would answer with every *other* embedding of
                // it besides — two pattern boxes on one host box among
                // them, which is an embedding like any other and not
                // the region this step is about. The match is a reading
                // of what `hoistable` already read, and `apply` judges
                // it like any other claim.
                let mut nodes = vec![id];
                nodes.extend(body.boxes.iter().copied());
                let mut inputs = self.graph.sources(id).to_vec();
                inputs.extend(body.outside.iter().copied());
                Ok(vec![Step {
                    rule: Rule::SelectHoist { body: body.graph },
                    dir: Direction::Forward,
                    at: Match {
                        nodes,
                        inputs,
                        sel: None,
                        follow: None,
                    },
                }])
            }
            RuleSpec::Concrete { rule, anchor, pin } => {
                let id = b
                    .get(*anchor)
                    .ok_or(TacticError::Unresolved { var: *anchor })?;
                let pair = rules::sides(rule).map_err(TacticError::Refused)?;
                Ok(find_pinned(self.graph, pair.lhs(), *pin, id)
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
            Region::Arm { cond, side } => arm_nodes(self.graph, *cond, *side).unwrap_or_default(),
        }
    }
}

// ---- arm membership --------------------------------------------------------------

/// Everything a box reads, transitively — the box included.
fn upstream(graph: &Graph, node: NodeId) -> HashSet<NodeId> {
    let mut seen = HashSet::new();
    let mut todo = vec![node];
    while let Some(node) = todo.pop() {
        if !seen.insert(node) {
            continue;
        }
        for src in graph.sources(node) {
            if let Source::Port { node, .. } = *src {
                todo.push(node);
            }
        }
    }
    seen
}

/// The boxes one side of a branch reads, plus the select itself: what a
/// tactic scoped to an arm may anchor on. `None` when nothing branches on
/// that wire any more — the branch collapsed, or never was.
///
/// Membership is the arm's **cone**, computed fresh at every asking:
/// everything upstream of this side's blocks, minus everything upstream
/// of the condition — the decided test's own making is what an arm is
/// scoped away from, and it is the one exclusion that matters,
/// since an enclosing split's condition feeds nothing but its own select
/// and so is never in a deeper arm's cone. The other side's boxes are out
/// by the same reading (nothing here reads them); **shared context is
/// in**: a split duplicates only what lies downstream of its
/// wire, so the very tests a nested split must reach — the hypothesis's
/// remaining unknowns — sit upstream, shared between the copies, and a
/// region that evicted what both arms read would make an arm that can
/// spend its hypothesis but never decompose it.
///
/// The select joins the region because every law of the branch layer is
/// read off it. The region scopes *anchors*, not windows — a law fired
/// from inside may still hold boxes outside in its match, and soundness is
/// [`rules::apply`]'s either way.
pub fn arm_nodes(graph: &Graph, cond: Source, side: bool) -> Option<HashSet<NodeId>> {
    let selects = branches_on(graph, cond);
    if selects.is_empty() {
        return None;
    }
    let block = |select: NodeId| graph.sources(select)[if side { 1 } else { 2 }];

    let mut region: HashSet<NodeId> = HashSet::new();
    for &select in &selects {
        if let Source::Port { node, .. } = block(select) {
            region.extend(upstream(graph, node));
        }
    }
    if let Source::Port { node, .. } = cond {
        for decided in upstream(graph, node) {
            region.remove(&decided);
        }
    }

    region.extend(selects);
    Some(region)
}

/// The branches a wire decides: the live `select`s reading `cond` at port
/// 0, and only the **outermost** of them — the ones no other lies inside.
///
/// Every answer of one source branch is its own `select`, so a wire decides
/// as many boxes as the branch left values, and every one of them is the
/// same branch. That is why this answers with a set rather than a box: an
/// arm is scoped by the *condition*, and taking one select for it would
/// scope to one of the answers and leave the rest of the arm outside.
///
/// A wire may also decide a branch **inside** one it already decides —
/// `specialize-choice` is the row that exists because an arm can retest
/// what the branch around it tested. Those are dropped: a select every
/// other candidate is upstream of is nested in them, and what an arm means
/// is the outermost reading. What is left is a set of peers, which is what
/// one branch comes to.
pub fn branches_on(graph: &Graph, cond: Source) -> Vec<NodeId> {
    let candidates: Vec<NodeId> = graph
        .live()
        .filter(|(id, kind)| {
            matches!(kind, NodeKind::Select) && graph.sources(*id).first() == Some(&cond)
        })
        .map(|(id, _)| id)
        .collect();
    // A nested retest is upstream of nothing here and downstream of the
    // branch that decided it, so it is exactly a candidate some other
    // candidate reaches.
    candidates
        .iter()
        .copied()
        .filter(|&here| {
            !candidates
                .iter()
                .any(|&other| other != here && upstream(graph, other).contains(&here))
        })
        .collect()
}

// ---- what a branch may grow over -------------------------------------------------

/// Everything the wires feed, transitively — the whole cone below them.
fn downstream(graph: &Graph, from: &[Source]) -> HashSet<NodeId> {
    let mut seen = HashSet::new();
    let mut todo = from.to_vec();
    while let Some(src) = todo.pop() {
        for sink in graph.sinks(src) {
            let Sink::Port { node, .. } = sink else {
                continue;
            };
            if !seen.insert(node) {
                continue;
            }
            for port in 0..graph.kind(node).arity().outputs {
                todo.push(Source::Port { node, port });
            }
        }
    }
    seen
}

/// The body a branch may grow forward over without swallowing another
/// branch: everything downstream of its answers **that is not itself a
/// `select`**, lifted out as a graph — the payload for a
/// [`Rule::SelectHoist`] that sorts branches towards the boundary rather
/// than copying them.
///
/// [`rules::propose`] reads the same law's body as the whole cone, and
/// the two readings are the whole difference between one firing a proof
/// asked for and the drive [`tree`] is. Stopping at a select is what
/// makes the second terminate in the shape it is named for: a select is
/// never duplicated, so the branches keep their count while the work
/// between them is pushed above them, one hoist at a time, until nothing
/// but a select or the boundary reads a select.
///
/// What comes back out is what anything **outside** the region reads of
/// it: a region box's port with a reader that is not a region box, and —
/// passed straight through, the way [`Rule::SelectHoist`] asks for it —
/// an answer read by the boundary or by a select the region left
/// standing. Both re-point onto the new select, which is what takes the
/// old one out of the program.
///
/// `None` where there is nothing to move, and where moving would be a
/// mistake:
///
/// - **Nothing downstream but branches.** The select is where a decision
///   tree wants it already.
/// - **A body reading what a branch below this one answers.** The step
///   would put down a select the body's own readers feed back into, so
///   the branch below is hoisted first. One always can be: blocking runs
///   downstream, and the cone below a select is finite, so the bottom of
///   any chain of blocked branches is a branch nothing blocks.
fn hoistable(graph: &Graph, select: NodeId) -> Option<Lifted> {
    if !matches!(graph.kind(select), NodeKind::Select) {
        return None;
    }
    let answers = vec![Source::Port {
        node: select,
        port: 0,
    }];

    // The region: transitive readers of the answers, with every select
    // left standing and not read through.
    let mut region: Vec<NodeId> = Vec::new();
    let mut todo = answers.clone();
    while let Some(src) = todo.pop() {
        for sink in graph.sinks(src) {
            let Sink::Port { node, .. } = sink else {
                continue;
            };
            if matches!(graph.kind(node), NodeKind::Select) || region.contains(&node) {
                continue;
            }
            region.push(node);
            for port in 0..graph.kind(node).arity().outputs {
                todo.push(Source::Port { node, port });
            }
        }
    }
    if region.is_empty() {
        return None;
    }
    let mine: HashSet<NodeId> = region.iter().copied().collect();

    // Nothing the region reads may be below the branch it is about to
    // move past — which it can only be by way of a select the region
    // stopped at.
    let below = downstream(graph, &answers);
    let reads_below = region
        .iter()
        .flat_map(|&node| graph.sources(node).iter().copied())
        .any(|src| match src {
            Source::Port { node, .. } => !mine.contains(&node) && below.contains(&node),
            Source::Input(_) => false,
        });
    if reads_below {
        return None;
    }

    // What is read from outside the region, region ports first and the
    // answers that pass straight through after them.
    let outside = |src: Source| {
        graph.sinks(src).iter().any(|sink| match sink {
            Sink::Output(_) => true,
            Sink::Port { node, .. } => !mine.contains(node),
        })
    };
    let mut leaves: Vec<Source> = Vec::new();
    let mut ports: Vec<NodeId> = region.clone();
    ports.sort_unstable();
    for node in ports {
        for port in 0..graph.kind(node).arity().outputs {
            let src = Source::Port { node, port };
            if outside(src) {
                leaves.push(src);
            }
        }
    }
    leaves.extend(answers.iter().copied().filter(|&src| outside(src)));
    if leaves.is_empty() {
        return None;
    }

    lift(graph, &region, &answers, &leaves)
}

// ---- resolving a stated match ----------------------------------------------------

/// [`MatchSpec`] × [`Bindings`] × the current graph → a concrete
/// [`Match`](rules::Match). Pure reading, and untrusted: the answer is
/// judged whole by [`rules::apply`], so a wrong resolution costs a refusal.
fn resolve(graph: &Graph, b: &Bindings, spec: &MatchSpec) -> Result<Match, TacticError> {
    let node_of = |v: Var| b.get(v).ok_or(TacticError::Unresolved { var: v });

    let mut nodes = Vec::with_capacity(spec.nodes.len());
    for &v in &spec.nodes {
        nodes.push(node_of(v)?);
    }

    let mut inputs = Vec::with_capacity(spec.inputs.len());
    for src in &spec.inputs {
        inputs.push(match src {
            SrcExpr::PortOf(v, port) => Source::Port {
                node: node_of(*v)?,
                port: *port,
            },
            SrcExpr::FeedOf(v, port) => {
                let node = node_of(*v)?;
                *graph
                    .sources(node)
                    .get(*port)
                    .ok_or(TacticError::OutOfRange {
                        var: *v,
                        port: *port,
                    })?
            }
            SrcExpr::Input(i) => Source::Input(*i),
            SrcExpr::Addressed(prefix, port) => {
                let node = match graph.lookup(prefix) {
                    Named::One(node) => node,
                    Named::Nothing => {
                        return Err(TacticError::NoSuchBox { at: prefix.clone() });
                    }
                    Named::Many(found) => {
                        return Err(TacticError::ManyBoxes {
                            at: prefix.clone(),
                            found,
                        });
                    }
                };
                if *port >= graph.kind(node).arity().outputs {
                    return Err(TacticError::NoSuchPort {
                        at: prefix.clone(),
                        port: *port,
                    });
                }
                Source::Port { node, port: *port }
            }
        });
    }

    Ok(Match {
        nodes,
        inputs,
        sel: None,
        follow: None,
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

/// One law, one box, one direction — [`Tactic::At`] with the canonical
/// pick, which is what the `.hant` surface `at(#7, not-not, backward)`
/// builds.
pub fn fire_at(at: Aim, law: Law, dir: Direction) -> Tactic {
    Tactic::At {
        at,
        law,
        dir,
        pick: Pick::First,
        readers: None,
    }
}

/// [`fire_at`], for some of the readers only — what a `for(...)` or
/// `except(...)` clause on an `at` builds.
pub fn fire_at_for(at: Aim, law: Law, dir: Direction, readers: Readers) -> Tactic {
    Tactic::At {
        at,
        law,
        dir,
        pick: Pick::First,
        readers: Some(readers),
    }
}

/// The whole table to fixpoint: the branch layer in its documented order,
/// the value layer behind it.
///
/// Shorter than it was by one list. The wiring laws were the third of it,
/// and there is no wiring left to spend — a value read twice is one box
/// with two readers the moment it is built, and a value read never is a
/// box the boundary does not reach.
///
/// This is the closest thing the tactic road has to a normalizer, and it
/// is still a strategy: those laws, in that order, everywhere they fire,
/// chosen here and replaceable by any proof that chooses differently.
pub fn decide() -> Tactic {
    Tactic::Repeat(
        Box::new(fire_first([rules::branching(), rules::folding()].concat())),
        None,
    )
}

/// The branch layer, spent to fixpoint.
///
/// The laws are tried in the order [`rules::branching`] documents. What
/// was advice in a doc comment is a program here.
pub fn branch_pass() -> Tactic {
    Tactic::Repeat(Box::new(fire_first(rules::branching())), None)
}

/// Every branch grown forward over everything but another branch, and
/// then out of every condition it stands in, to fixpoint: the
/// **decision tree**.
///
/// Two rows, tried in that order. `select-hoist` says that what runs
/// after a branch runs inside whichever arm the branch takes; spent
/// everywhere it will go, with [`hoistable`]'s reading of the body — the
/// cone below a select, every other select left standing — it sorts a
/// graph into two halves: the work, which reads nothing a branch
/// answers, and the branches, which read the work and each other.
/// `cond-hoist` is the row for the one port that leaves behind: a
/// branch whose **condition** is what another branch answered runs
/// under that branch instead, once per block it chooses between.
///
/// Between them the fixpoint is two sentences. No box but a select
/// reads what a select answers, so nothing computes from an answer; and
/// no select turns on what a select answered, so every condition in the
/// graph is select-free — a test of the work, decided before any branch
/// runs. That is a decision tree said in a graph.
///
/// The order is what makes the second row cheap and the drive easy to
/// read. A `cond-hoist` is offered only in a round where no branch has
/// anything to grow over, so by the time one fires every reader of an
/// answer is already a select and what the step copies is a **branch**,
/// never work. Nor can it hand the first row anything back: the copies
/// are read by the select it puts down, that select is read by whoever
/// read the branch that moved — selects, all of them — and no box that
/// is not a select gains an answer to read. So the drive is one phase
/// and then the other, however the rounds interleave.
///
/// It **grows** a graph, which is why no list drives either row and why
/// this is a tactic a proof names rather than something `decide` runs. A
/// branch's body goes into both arms, so a value under `n` branches ends
/// up written `2^n` times in the worst case, and the worst case is a
/// real program: this is for a goal that wants its cases laid out, not
/// for tidying a large one.
///
/// It terminates, a phase at a time.
///
/// The hoisting phase's measure is what the copies read. A hoist
/// replaces each body box with two boxes reading that branch's blocks
/// instead of its answers, so each copy has strictly fewer branches
/// above it than the box it came from, and no box outside the body
/// gains one. A multiset of naturals with one member replaced by
/// finitely many smaller ones is a decreasing multiset, and the branch
/// that fired loses its last reader and drops out of the program.
///
/// **That argument is not complete, and it used to be.** It leaned on
/// "a select is never copied, so the branches keep their count", which
/// was true while a select carried every answer: a hoist took one
/// select to one select, however wide. A select carries one answer now,
/// so a hoist over a region leaving `m` of them puts down `m` selects
/// where it found one, and the multiset gains `m - 1` members at the
/// branch-count of the one it lost rather than below it. Nothing here
/// is known to diverge — the copies are read only by the selects the
/// step puts down, and nothing upstream of the branch changes — but the
/// measure needs restating before that is a proof rather than a
/// reading. Until it is, what holds the drive is the test: `tree` is
/// run over bodies with branches in branches, and before is compared
/// against after **on the machine**, at every assignment.
///
/// The condition phase's measure is the graph read as the term it
/// unfolds to, weighted so that a condition costs what it decides:
/// `μ(op(t̄)) = 1 + Σμ(tᵢ)` and `μ(select(c, t̄, ē)) = μ(c)·(1 + Σμ(t̄) +
/// Σμ(ē))`. A firing takes `μ(c)·(1 + μ(t) + μ(e))·K` to `μ(c)·(1 +
/// μ(t)·K + μ(e)·K)` for `K = 1 + μ(T) + μ(E)`, which is smaller by
/// `μ(c)·(K - 1)` — and `K` is at least 3, since a block weighs at
/// least one. The unfolding is finite because the graph is acyclic, and
/// a firing is one such conversion at every occurrence it is shared at,
/// so an endless drive would be an endless run on the unfolding.
pub fn tree() -> Tactic {
    let branches = || Query::new().is("sel", query::NodePred::Kind(query::KindPat::Select));
    Tactic::Repeat(
        Box::new(Tactic::First(vec![
            Tactic::Fire {
                at: branches(),
                rule: RuleSpec::Hoist { anchor: Var("sel") },
                pick: Pick::First,
            },
            // Read off rather than stated: the payload is three widths,
            // and the box the pattern anchors at is the branch that made
            // the condition, which `propose` finds from the branch that
            // moves.
            Tactic::Fire {
                at: branches(),
                rule: RuleSpec::ReadOff {
                    laws: vec![Law::CondHoist],
                    anchor: Var("sel"),
                },
                pick: Pick::First,
            },
        ])),
        None,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::term::{Context, Prim};
    use crate::kernel::{build, rules::replay};
    use crate::query::{KindPat, NodePred};
    use bytecode::{Value, assemble};
    use std::collections::HashMap;

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
        let term = crate::kernel::term::lower(&mut terms, &library, idx).unwrap();
        let graph = build(&terms, term);
        graph.check().unwrap();
        graph
    }

    /// What a proof would write to name that box: as much of its address
    /// as the listing emphasises.
    fn named(graph: &Graph, id: NodeId) -> Prefix {
        Prefix::parse(&graph.shortest(id)).expect("a listing's own spelling")
    }

    /// A graph arrives with nothing to sweep.
    ///
    /// Every one of these bodies is a wiring exercise — two crossings
    /// that cancel, a `pick` that copies, a `drop` that discards — and
    /// every one lands as the values it computes and no boxes besides.
    /// There is no run to make, which is the strongest form of a run
    /// always terminating.
    #[test]
    fn a_built_graph_has_no_wiring_to_sweep() {
        for (body, boxes) in [
            ("swap swap", 0),
            ("dip { swap } swap dip { swap }", 0),
            ("push 9 pick 0", 1),
            // The comparison is computed and then dropped, so the
            // boundary names nothing of it and nothing of it is there.
            ("pick 1 pick 1 equal drop 0", 0),
        ] {
            let graph = built(body);
            graph.check().unwrap_or_else(|e| panic!("{}: {}", body, e));
            assert_eq!(graph.live_count(), boxes, "{}:\n{}", body, graph);
        }
        // The crossings cancel by never having been written: what the
        // boundary leaves is what it was handed, in the order it was
        // handed it.
        let graph = built("swap swap");
        assert_eq!(graph.outputs(), [Source::Input(0), Source::Input(1)]);
    }

    /// A run of the whole table leaves a graph, the run is its own
    /// derivation, and a second run has nothing left to do.
    #[test]
    fn a_run_is_a_derivation_that_replays() {
        for body in [
            "pick 1 pick 1 equal drop 0",
            "branch { pick 0 drop 0 not } { not }",
            "push true branch { push 1 } { push 2 }",
            "push 1 push 2 add",
        ] {
            let original = built(body);
            let mut graph = original.clone();
            let mut deriv = Derivation::default();
            run(&mut graph, &mut deriv, &decide()).unwrap_or_else(|e| panic!("{}: {}", body, e));
            graph
                .check()
                .unwrap_or_else(|e| panic!("{}: left a torn graph: {}", body, e));

            let mut again = Derivation::default();
            assert_eq!(
                run(&mut graph, &mut again, &decide()),
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
        }
    }

    /// A program of literals is the values it computes, and `decide`
    /// runs it out: a window whose every operand is a `push` lands on the
    /// pushes of its answer, and there is nothing else left.
    ///
    /// `tuple 0` is the row this was widened for. It reads no operand, so
    /// every operand it reads is a literal — vacuously, which is still
    /// the side condition — and a driver that wanted a literal behind the
    /// box to anchor at would never fire it.
    #[test]
    fn a_window_of_literals_lands_on_its_answer() {
        let unit = Value::unit();
        let pair = |a: Value, b: Value| Value::Tuple(vec![a, b]);
        for (body, answers) in [
            ("tuple 0", vec![unit.clone()]),
            (
                "push 1 push 2 tuple 2",
                vec![pair(Value::Int(1), Value::Int(2))],
            ),
            // The empty tuple built and then built into another: the fold
            // reaches the second window once the first has answered.
            (
                "push 1 tuple 0 tuple 2",
                vec![pair(Value::Int(1), unit.clone())],
            ),
            // A literal taken apart is its parts — and one that is no
            // tuple is the `()`s the machine fills the slots with, which
            // is the machine's junk and not a second opinion.
            ("push (1, 2) untuple 2", vec![Value::Int(1), Value::Int(2)]),
            ("push 7 untuple 2", vec![unit.clone(), unit.clone()]),
            // Round trip and arithmetic behind it: three windows, and
            // what is left is the number.
            ("push 3 push 4 tuple 2 untuple 2 add", vec![Value::Int(7)]),
        ] {
            let mut graph = built(body);
            let mut deriv = Derivation::default();
            run(&mut graph, &mut deriv, &decide()).unwrap_or_else(|e| panic!("{}: {}", body, e));
            graph
                .check()
                .unwrap_or_else(|e| panic!("{}: left a torn graph: {}", body, e));
            assert!(
                graph
                    .live()
                    .all(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Push(_)))),
                "{}: an operation survived the fold:\n{}",
                body,
                graph
            );
            let left: Vec<Value> = graph
                .outputs()
                .iter()
                .map(|src| match src {
                    Source::Port { node, port } => match graph.kind(*node) {
                        NodeKind::Op(Prim::Push(v)) if *port == 0 => v.clone(),
                        kind => panic!("{}: the boundary reads {}:\n{}", body, kind, graph),
                    },
                    Source::Input(_) => panic!("{}: a closed graph has no inputs", body),
                })
                .collect();
            assert_eq!(left, answers, "{}: the wrong answer:\n{}", body, graph);
        }
    }

    /// The directed spelling: fold the literal condition, claiming there
    /// is exactly one.
    ///
    /// And what a fold leaves: the untaken arm's literal is not
    /// *deleted*, it is simply not reached. There is no cleanup pass,
    /// focused or otherwise — the boundary stops naming it and it stops
    /// being part of the program in the same move.
    #[test]
    fn a_literal_condition_keeps_its_arm() {
        let mut graph = built("push true branch { push 1 } { push 2 }");
        let mut deriv = Derivation::default();
        let tactic = Tactic::Fire {
            at: Query::new()
                .is("sel", NodePred::Kind(KindPat::Select))
                .is("lit", NodePred::Kind(KindPat::AnyPush))
                .feeds("lit", 0, "sel", 0),
            rule: RuleSpec::ReadOff {
                laws: vec![Law::SelectLiteral],
                anchor: Var("sel"),
            },
            pick: Pick::Unique,
        };
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();
        assert_eq!(deriv.len(), 1, "one fold and no sweeping after it");
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

    /// An arm region: after a case split, each side of the fresh branch
    /// is its own focus — the pinned literal and that side's copy of the
    /// body in, the condition op and the other side out, the select in
    /// because the branch layer's laws anchor there. A fire scoped to the
    /// then side folds its copy and leaves the other standing.
    #[test]
    fn an_arm_region_holds_a_fire_to_its_side() {
        let mut graph = built("is_bool not");
        let mut deriv = Derivation::default();
        let test = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::IsBool)))
            .map(|(id, _)| id)
            .expect("the split target");
        let cond = rules::case_split(&mut graph, &mut deriv, test)
            .expect("the split lands")
            .expect("there is a split to make");

        let is_bool = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::IsBool)))
            .map(|(id, _)| id)
            .expect("the answer box survives the split");
        let then_region = arm_nodes(&graph, cond, true).expect("the branch is live");
        let else_region = arm_nodes(&graph, cond, false).expect("the branch is live");
        assert!(
            !then_region.contains(&is_bool) && !else_region.contains(&is_bool),
            "the condition belongs to no arm"
        );
        assert!(then_region.iter().all(|n| {
            *graph.kind(*n) != NodeKind::Op(Prim::Push(bytecode::Value::Bool(false)))
        }));
        assert_eq!(
            then_region.intersection(&else_region).count(),
            1,
            "the arms share only the select"
        );

        // A fold scoped to the then arm spends its copy of the body —
        // `not` of the pinned `true` — and leaves the else copy standing.
        let scoped = Tactic::Within(
            Region::Arm { cond, side: true },
            Box::new(fire_first(vec![Law::Fold])),
        );
        run(&mut graph, &mut deriv, &scoped).unwrap();
        graph.check().unwrap();
        let nots = graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Not)))
            .count();
        assert_eq!(nots, 1, "only the then copy folded:\n{}", graph);
        assert_eq!(deriv.len(), 4, "the split's three rows and one scoped fold");
    }

    /// A branch that is gone resolves to the empty region, which binds
    /// nothing: a fire scoped to it fails loudly and the graph stands.
    #[test]
    fn a_vanished_branch_is_an_empty_region() {
        let mut graph = built("push true branch { push 1 } { push 2 }");
        let cond = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Select))
            .map(|(id, _)| graph.sources(id)[0])
            .expect("the branch as built");
        assert!(arm_nodes(&graph, cond, true).is_some());

        let mut deriv = Derivation::default();
        run(
            &mut graph,
            &mut deriv,
            &fire_first(vec![Law::SelectLiteral]),
        )
        .unwrap();
        assert!(
            arm_nodes(&graph, cond, true).is_none(),
            "the fold spent the branch"
        );

        let before = graph.clone();
        let scoped = Tactic::Within(
            Region::Arm { cond, side: true },
            Box::new(fire_first(vec![Law::SelectLiteral])),
        );
        assert!(matches!(
            run(&mut graph, &mut deriv, &scoped),
            Err(TacticError::NothingFound { .. })
        ));
        assert_eq!(graph, before, "a scoped miss lands nothing");
    }

    /// A failed alternative leaves no trace, and — the point of cloning
    /// rather than undoing — what the run records still replays from the
    /// original graph, first try to last step.
    #[test]
    fn speculation_leaves_no_trace() {
        let original = built("push 1 push 2 add push 3 add");
        let mut graph = original.clone();
        let mut deriv = Derivation::default();
        // The first alternative advances one step and then dies looking
        // for a branch that is not there.
        let doomed = Tactic::Seq(vec![
            fire_first(vec![Law::Fold]),
            Tactic::Fire {
                at: Query::new().is("f", NodePred::Kind(KindPat::Select)),
                rule: RuleSpec::ReadOff {
                    laws: vec![Law::SelectSame],
                    anchor: Var("f"),
                },
                pick: Pick::First,
            },
        ]);
        let winner = Tactic::Repeat(Box::new(fire_first(vec![Law::Fold])), None);
        let tactic = Tactic::First(vec![doomed, winner]);
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 1, "one literal left:\n{}", graph);
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
            at: Query::new().is("f", NodePred::Kind(KindPat::Select)),
            rule: RuleSpec::ReadOff {
                laws: vec![Law::SelectSame],
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
        let original = built("push 1 push 2 add push 3 add");
        let mut graph = original.clone();
        let mut deriv = Derivation::default();
        let tactic = Tactic::Repeat(Box::new(fire_first(vec![Law::Fold])), Some(1));
        assert_eq!(
            run(&mut graph, &mut deriv, &tactic),
            Err(TacticError::OutOfFuel { after: 1 })
        );
        // Both folds landed before the wire tripped, and both stand.
        graph.check().unwrap();
        assert_eq!(deriv.len(), 2);
        let mut fresh = original.clone();
        let steps: Vec<Step> = deriv.steps().cloned().collect();
        replay(&mut fresh, &steps).unwrap();
        assert_eq!(fresh, graph);
    }

    /// `Unique` counts what `First` orders: two offers are two, and
    /// claiming uniqueness where there is a choice is refused loudly.
    #[test]
    fn unique_counts_what_first_orders() {
        let graph = built("push 1 push 2 add push 3 push 4 add");
        let folds = |pick| Tactic::Fire {
            at: Query::new().is("a", NodePred::Kind(KindPat::Op(Some(Prim::Add)))),
            rule: RuleSpec::ReadOff {
                laws: vec![Law::Fold],
                anchor: Var("a"),
            },
            pick,
        };
        let mut probe = graph.clone();
        let mut deriv = Derivation::default();
        assert_eq!(
            run(&mut probe, &mut deriv, &folds(Pick::Unique)),
            Err(TacticError::Ambiguous { found: 2 })
        );
        assert!(deriv.is_empty(), "a refused pick lands nothing");
        assert_eq!(probe, graph);

        let mut probe = graph.clone();
        let mut deriv = Derivation::default();
        assert_eq!(
            run(&mut probe, &mut deriv, &folds(Pick::First)),
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
        let mut graph = built("not not");
        let mut deriv = Derivation::default();
        // Pattern box 1 is `not-not`'s *second* `not`, so the only box
        // this can be pinned to is the outer one — the inner `not` is
        // bound first and offers nothing.
        let tactic = Tactic::Fire {
            at: Query::new().is("n", NodePred::Kind(KindPat::Op(Some(Prim::Not)))),
            rule: RuleSpec::Concrete {
                rule: Rule::NotNot,
                anchor: Var("n"),
                pin: 1,
            },
            pick: Pick::First,
        };
        run(&mut graph, &mut deriv, &tactic).unwrap();
        graph.check().unwrap();
        assert_eq!(deriv.len(), 1);
        assert_eq!(graph.live_count(), 1, "the coercion, alone:\n{}", graph);
        assert!(matches!(
            graph.live().next().unwrap().1,
            NodeKind::Op(Prim::AsBool)
        ));
    }

    /// The branch layer, spent as a program: a branch whose arms answer
    /// alike dissolves to the one arm, and a literal condition keeps its
    /// own.
    #[test]
    fn the_branch_layer_is_a_pass() {
        // `branch { add } { add }` arrives with one `add` in it — both
        // arms were handed the same sources — so the pass is one
        // `select-same`, and what it leaves is that `add` answering for
        // itself: the box, and the boundary reading it.
        let mut graph = built("branch { add } { add }");
        let mut deriv = Derivation::default();
        run(&mut graph, &mut deriv, &branch_pass()).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 1, "\n{}", graph);
        let (id, kind) = graph.live().next().unwrap();
        assert_eq!(kind, &NodeKind::Op(Prim::Add));
        assert_eq!(
            graph.outputs(),
            [Source::Port { node: id, port: 0 }],
            "the answer is the arm's, not the condition:\n{}",
            graph
        );

        // And β: the literal keeps its arm. The whole content is what
        // `truthy` computes, so the claim here is the shape.
        let mut graph = built("push true branch { push 1 } { push 2 }");
        let mut deriv = Derivation::default();
        run(&mut graph, &mut deriv, &branch_pass()).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 1, "\n{}", graph);
        let (_, kind) = graph.live().next().unwrap();
        assert_eq!(kind, &NodeKind::Op(Prim::Push(Value::Int(1))));
    }

    /// Whether every condition in the graph is select-free: no select
    /// turns on what a select answered.
    ///
    /// With [`bunched`] holding, nothing between them either — a box
    /// that is not a select reads no answer at all — so the two
    /// together say a condition is decided before any branch runs.
    fn decided_first(graph: &Graph) -> bool {
        graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select))
            .all(|(id, _)| match graph.sources(id)[0] {
                Source::Port { node, .. } => !matches!(graph.kind(node), NodeKind::Select),
                _ => true,
            })
    }

    /// Whether every branch is where a decision tree wants it: nothing
    /// but another select, or the boundary, reads what a select answers.
    fn bunched(graph: &Graph) -> bool {
        graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select))
            .flat_map(|(id, kind)| {
                (0..kind.arity().outputs).map(move |port| Source::Port { node: id, port })
            })
            .flat_map(|src| graph.sinks(src))
            .all(|sink| match sink {
                crate::kernel::graph::Sink::Output(_) => true,
                crate::kernel::graph::Sink::Port { node, .. } => {
                    matches!(graph.kind(node), NodeKind::Select)
                }
            })
    }

    /// The decision tree, run to its fixpoint: what the drive is *for* is
    /// the shape it leaves, and the shape is one sentence — no box but a
    /// select reads what a select answers.
    ///
    /// The wiring settles nothing here, for the reason it settles nothing
    /// about `select-hoist`: a branch is a choice per output, and pushing
    /// an application through one is the whole content of the law. The law
    /// itself is held to the machine in [`rules`]; what is claimed here is
    /// that the drive spends it to the shape it is named for, and that
    /// what it did replays.
    #[test]
    fn a_tree_leaves_the_branches_at_the_output() {
        for (body, selects) in [
            // One branch and one box after it: the branch grows over the
            // `negate`, which is the corpus's own `select-hoist` claim.
            ("branch { not } { as_bool } negate", 1),
            // Work between two branches and work after both. Every box of
            // it ends up above every branch — and the second branch turned
            // on what the first answered, so it splits in two under it.
            (
                "pick 1 branch { not } { as_bool } negate branch { negate } { not } is_int",
                3,
            ),
            // A branch whose answer two boxes read, one of them the
            // condition of the branch after it — so the second branch
            // splits under the first. **Five**, where a wider select left
            // four: the region the first branch grows over leaves two
            // answers, and a branch is a select per answer, so what comes
            // down is two selects rather than one two-wide one.
            (
                "pick 0 branch { not } { as_bool } pick 0 is_bool branch { negate } { not }",
                5,
            ),
        ] {
            let mut graph = built(body);
            let mut deriv = Derivation::default();
            let before = graph.clone();
            run(&mut graph, &mut deriv, &tree()).expect(body);
            graph.check().unwrap_or_else(|e| panic!("{}: {}", body, e));
            assert!(
                bunched(&graph),
                "{}: a branch is still read by something that is not one:\n{}",
                body,
                graph
            );
            assert!(
                decided_first(&graph),
                "{}: a branch still turns on what a branch answered:\n{}",
                body,
                graph
            );
            assert_eq!(
                graph
                    .live()
                    .filter(|(_, k)| matches!(k, NodeKind::Select))
                    .count(),
                selects,
                "{}: a select was copied or lost:\n{}",
                body,
                graph
            );
            // What the count cannot say: that the tree is the same program.
            // The rows the drive spends are held to the machine one at a
            // time in [`rules`], and this is the drive as a whole held to
            // it — every assignment, before against after.
            for values in rules::tests::samples(graph.arity().inputs) {
                assert_eq!(
                    rules::tests::eval_on(&before, &values),
                    rules::tests::eval_on(&graph, &values),
                    "{}: the tree is a different program on {:?}",
                    body,
                    values
                );
            }
            // Every step of it is a checked instance of the table, and
            // the run is a derivation like any other.
            let mut again = before;
            let steps: Vec<Step> = deriv.steps().cloned().collect();
            replay(&mut again, &steps).unwrap_or_else(|e| panic!("{}: {}", body, e));
            assert_eq!(again, graph, "{}: the run does not replay", body);
        }
    }

    /// A graph with no branch in it has nothing for the drive to spend,
    /// and saying so is not a failure: a `Repeat` whose body finds
    /// nothing on its first round is done rather than broken.
    #[test]
    fn a_tree_of_no_branches_is_the_graph_itself() {
        let original = built("push 1 push 2 add");
        let mut graph = original.clone();
        let mut deriv = Derivation::default();
        assert_eq!(
            run(&mut graph, &mut deriv, &tree()),
            Ok(Progress::Unchanged)
        );
        assert_eq!(graph, original);
        assert_eq!(deriv.len(), 0);
    }

    /// The order the drive has to find for itself: a branch whose body
    /// reads what a branch **below** it answers cannot go first.
    ///
    /// `S` answers a wire that a `not` and an `add` read; the `not`
    /// decides `T`, and the `add` reads `T`'s answer as well. Hoisting
    /// `S` first would hand the `add`'s readers a new select the `add`
    /// itself feeds back into, so [`hoistable`] declines it and offers
    /// `T` instead — after which `S` has nothing below it and goes.
    #[test]
    fn a_branch_below_is_hoisted_first() {
        let mut graph = Graph::empty(5);
        let answered = graph.add(NodeKind::Select, (0..3).map(Source::Input).collect());
        let decided = graph.add(NodeKind::Op(Prim::Not), vec![answered[0]]);
        let inner = graph.add(
            NodeKind::Select,
            vec![decided[0], Source::Input(3), Source::Input(4)],
        );
        let summed = graph.add(NodeKind::Op(Prim::Add), vec![answered[0], inner[0]]);
        graph.close(summed);
        graph.check().unwrap();
        let before = graph.clone();

        let select = |graph: &Graph, at: usize| {
            graph
                .live()
                .filter(|(_, k)| matches!(k, NodeKind::Select))
                .map(|(id, _)| id)
                .nth(at)
                .expect("a branch")
        };
        let outer = select(&graph, 0);
        assert!(
            hoistable(&graph, outer).is_none(),
            "the outer branch's body reads what the inner one answers:\n{}",
            graph
        );
        assert!(hoistable(&graph, select(&graph, 1)).is_some());

        let mut deriv = Derivation::default();
        run(&mut graph, &mut deriv, &tree()).expect("the inner branch goes first");
        graph.check().unwrap();
        assert!(bunched(&graph), "\n{}", graph);
        assert!(decided_first(&graph), "\n{}", graph);
        // Five: the region `S` grew over — the `not` and the `add` —
        // leaves two answers, and a branch is a select per answer, so two
        // came down where a two-wide select was one; `T` split in two
        // underneath, and `S` itself is the fifth.
        assert_eq!(
            graph
                .live()
                .filter(|(_, k)| matches!(k, NodeKind::Select))
                .count(),
            5,
            "\n{}",
            graph
        );
        // And it is the same program, which is what the count stands in
        // for: the sorted branches answer what the nested ones did.
        for values in rules::tests::samples(5) {
            assert_eq!(
                rules::tests::eval_on(&before, &values),
                rules::tests::eval_on(&graph, &values),
                "the sorted branches are a different program on {:?}",
                values
            );
        }
    }

    /// The one address that is a **name** rather than a description, and
    /// what it is for: two boxes offer the same law, and the proof says
    /// which. `fire` takes the first it is offered and has no way to say
    /// anything else.
    #[test]
    fn a_named_box_is_where_the_step_lands() {
        let graph = built("push 1 push 2 add push 3 push 4 add");
        let adds: Vec<NodeId> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Add)))
            .map(|(id, _)| id)
            .collect();
        assert_eq!(adds.len(), 2, "two folds to choose between:\n{}", graph);

        for &target in &adds {
            let mut g = graph.clone();
            let mut deriv = Derivation::default();
            let fired = run(
                &mut g,
                &mut deriv,
                &fire_at(
                    Aim::Box(named(&graph, target)),
                    Law::Fold,
                    Direction::Forward,
                ),
            )
            .unwrap();
            assert_eq!(fired, Progress::Advanced(1));
            assert!(!g.is_live(target), "the named `add` went:\n{}", g);
            for &other in &adds {
                assert!(
                    other == target || g.is_live(other),
                    "and only the named one:\n{}",
                    g
                );
            }
            // Checked like every other step, and a record that replays.
            replay(
                &mut graph.clone(),
                &deriv.steps().cloned().collect::<Vec<_>>(),
            )
            .unwrap();
        }

        // What the un-addressed spelling does instead.
        let mut g = graph.clone();
        let mut deriv = Derivation::default();
        run(&mut g, &mut deriv, &fire_first(vec![Law::Fold])).unwrap();
        assert!(!g.is_live(adds[0]), "the first, always:\n{}", g);
    }

    /// A match counts when it holds the named box **anywhere** in its
    /// image, not only where the law's pattern anchors. `not-not`'s
    /// pattern is `not ; not` and it anchors on the first, so `propose`
    /// seeded at the second offers nothing — and naming the second fires
    /// all the same, which is the whole difference between an address and
    /// a seed.
    #[test]
    fn the_named_box_need_not_be_where_the_pattern_anchors() {
        let mut graph = built("not not");
        let nots: Vec<NodeId> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Not)))
            .map(|(id, _)| id)
            .collect();
        let [first, second] = nots[..] else {
            panic!("two nots, back to back:\n{}", graph)
        };
        assert!(
            rules::propose(&graph, &[Law::NotNot], second).is_empty(),
            "the pattern anchors on the first `not`"
        );

        let mut deriv = Derivation::default();
        let step = fire_at(
            Aim::Box(named(&graph, second)),
            Law::NotNot,
            Direction::Forward,
        );
        run(&mut graph, &mut deriv, &step).unwrap();
        assert_eq!(deriv.len(), 1);
        assert!(
            !graph.is_live(first) && !graph.is_live(second),
            "both nots went, the pair being what the law spends:\n{}",
            graph
        );
    }

    /// And the exception that keeps *that* honest. `select-hoist` carries
    /// the whole cone below the branch it moves, so a box in that cone is
    /// in the window of every branch above it too — and a match holding
    /// the named box "anywhere" would be an equation about one of those
    /// other branches, picked because a payload box matched. The named
    /// box is the branch that moves.
    #[test]
    fn a_region_carrying_law_anchors_at_the_box_named() {
        let graph = built("branch { not } { as_bool } branch { not } { as_bool } negate");
        let selects: Vec<NodeId> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select))
            .map(|(id, _)| id)
            .collect();
        let [above, moving] = selects[..] else {
            panic!(
                "two branches, one reading what the other answers:\n{}",
                graph
            )
        };

        let mut g = graph.clone();
        let mut deriv = Derivation::default();
        run(
            &mut g,
            &mut deriv,
            &fire_at(
                Aim::Box(named(&graph, moving)),
                Law::SelectHoist,
                Direction::Forward,
            ),
        )
        .unwrap();
        assert_eq!(deriv.len(), 1);
        // The branch named is the one that spent itself; the one above it
        // is untouched, its cone having held the named box only as
        // payload.
        assert!(
            !g.is_live(moving) && g.is_live(above),
            "the branch named moved and the one above it stood:\n{}",
            g
        );
    }

    /// The direction is the author's, and `backward` reads the law's
    /// equation right to left.
    ///
    /// A right-hand side is looked for like anything else, because
    /// nothing splits readers — here `as_bool`, read back as the two
    /// `not`s it is.
    #[test]
    fn a_named_box_can_be_rewritten_backward() {
        // A `not` for the payload to be read off, and the `as_bool` the
        // law's right side is, standing apart from it.
        let graph = built("pick 0 not swap as_bool tuple 2");
        let (coercion, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::AsBool)))
            .expect("the coercion");

        let mut g = graph.clone();
        let mut deriv = Derivation::default();
        run(
            &mut g,
            &mut deriv,
            &fire_at(
                Aim::Box(named(&graph, coercion)),
                Law::NotNot,
                Direction::Backward,
            ),
        )
        .unwrap();
        let landed: Vec<Step> = deriv.steps().cloned().collect();
        let [step] = &landed[..] else {
            panic!("one step")
        };
        assert_eq!(step.dir, Direction::Backward);
        assert_eq!(step.rule.law(), Law::NotNot);
        assert_eq!(
            g.live()
                .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Not)))
                .count(),
            2,
            // Two, not three: the inner `not` the law puts back is the
            // `not` this graph already had, because that is what it is.
            "the coercion came back as the two `not`s it is:\n{}",
            g
        );
        replay(&mut graph.clone(), &landed).unwrap();
    }

    /// The two ways a named address fails, said apart — because they are
    /// different mistakes. A box that is not there is a proof reading a
    /// listing from before the step in front of it; a box that is there
    /// A branch is `n` boxes now, and `selects-on` is how a proof names
    /// the lot without knowing `n` or reading `n` addresses off a report.
    ///
    /// The load-bearing part is that it fires at the branch **as it stood**
    /// and not at what it leaves. `select-hoist` puts down a fresh select
    /// on the very same condition per answer its region leaves, so a step
    /// that re-read the set between firings would find its own answers and
    /// keep going; the set is read once and kept as addresses, so two
    /// answers is two firings.
    #[test]
    fn selects_on_fires_once_at_every_answer_of_a_branch() {
        // A branch leaving two answers, a `negate` after each: two peer
        // selects on `in0`, each with something to grow over.
        let graph = built("branch { push 1 push 3 } { push 2 push 4 } negate roll 1 negate roll 1");
        let selects: Vec<NodeId> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select))
            .map(|(id, _)| id)
            .collect();
        assert_eq!(selects.len(), 2, "one select per answer:\n{}", graph);
        for &id in &selects {
            assert_eq!(graph.sources(id)[0], Source::Input(0), "\n{}", graph);
        }

        let mut g = graph.clone();
        let mut deriv = Derivation::default();
        let fired = run(
            &mut g,
            &mut deriv,
            &fire_at(
                Aim::SelectsOn(Wire::Input(0)),
                Law::SelectHoist,
                Direction::Forward,
            ),
        )
        .expect("both answers hoist");
        assert_eq!(fired, Progress::Advanced(2), "once per answer:\n{}", g);
        g.check().unwrap();

        // Both `negate`s are inside the arms now, two copies apiece, and
        // the branch is still one branch: every select on the condition.
        assert_eq!(
            g.live()
                .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Negate)))
                .count(),
            4,
            "each `negate` went into both arms:\n{}",
            g
        );
        for (id, kind) in g.live() {
            if matches!(kind, NodeKind::Select) {
                assert_eq!(g.sources(id)[0], Source::Input(0), "\n{}", g);
            }
        }

        // Aimed at one of them by name, only that one moves — the set is
        // the whole of what `selects-on` adds.
        let mut one = graph.clone();
        run(
            &mut one,
            &mut Derivation::default(),
            &fire_at(
                Aim::Box(named(&graph, selects[0])),
                Law::SelectHoist,
                Direction::Forward,
            ),
        )
        .expect("one answer hoists");
        assert_eq!(
            one.live()
                .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Negate)))
                .count(),
            3,
            "one `negate` doubled and the other did not:\n{}",
            one
        );
    }

    /// A wire nothing branches on is its own sentence: the wire is there,
    /// and no `select` turns on it. Said apart from an address no box
    /// answers to, which is a different mistake.
    #[test]
    fn a_wire_no_branch_turns_on_is_named() {
        let graph = built("not not");
        assert_eq!(
            run(
                &mut graph.clone(),
                &mut Derivation::default(),
                &fire_at(
                    Aim::SelectsOn(Wire::Input(0)),
                    Law::SelectHoist,
                    Direction::Forward
                ),
            ),
            Err(TacticError::NoSelectsOn {
                wire: Wire::Input(0)
            })
        );
        assert_eq!(
            TacticError::NoSelectsOn {
                wire: Wire::Input(0)
            }
            .to_string(),
            "no live branch of this side turns on in0"
        );

        // And an address inside the aim fails by name, like every other.
        let ghost = Prefix::parse("zzzzzzzzzzzz").expect("an address of nought");
        assert_eq!(
            run(
                &mut graph.clone(),
                &mut Derivation::default(),
                &fire_at(
                    Aim::SelectsOn(Wire::Port(ghost.clone(), 0)),
                    Law::SelectHoist,
                    Direction::Forward
                ),
            ),
            Err(TacticError::NoSuchBox { at: ghost })
        );
    }

    /// with nothing to fire on it is a proof naming the wrong law.
    #[test]
    fn a_named_address_fails_by_name() {
        let graph = built("not not");
        let (live, _) = graph.live().next().expect("boxes");

        let ghost = Prefix::parse("zzzzzzzzzzzz").expect("an address of nought");
        assert_eq!(graph.lookup(&ghost), Named::Nothing, "\n{}", graph);
        assert_eq!(
            run(
                &mut graph.clone(),
                &mut Derivation::default(),
                &fire_at(Aim::Box(ghost.clone()), Law::NotNot, Direction::Forward),
            ),
            Err(TacticError::NoSuchBox { at: ghost })
        );

        assert_eq!(
            run(
                &mut graph.clone(),
                &mut Derivation::default(),
                &fire_at(
                    Aim::Box(named(&graph, live)),
                    Law::EqualRefl,
                    Direction::Forward
                ),
            ),
            Err(TacticError::NoMatchAt {
                at: graph.address(live),
                law: Law::EqualRefl,
                dir: Direction::Forward,
            })
        );
        assert_eq!(
            TacticError::NoMatchAt {
                at: graph.address(live),
                law: Law::EqualRefl,
                dir: Direction::Backward,
            }
            .to_string(),
            format!(
                "no backward `equal-refl` match holds {}",
                graph.address(live)
            )
        );
    }

    /// A prefix is a name only while it means one box, and when it means
    /// several the step says which — the answer being to write more of it.
    #[test]
    fn an_address_that_names_two_boxes_says_so() {
        // Seventeen boxes against sixteen letters: two of them start the
        // same way, whatever the letters turn out to be.
        let graph = built(
            "push 1 push 2 add push 3 add push 4 add push 5 add push 6 add \
             push 7 add push 8 add push 9 add",
        );
        assert!(graph.live_count() > 16, "\n{}", graph);
        let mut sharing: HashMap<char, Vec<NodeId>> = HashMap::new();
        for (id, _) in graph.live() {
            let first = graph.address(id).letters().chars().next().expect("letters");
            sharing.entry(first).or_default().push(id);
        }
        let (&letter, held) = sharing
            .iter()
            .find(|(_, held)| held.len() > 1)
            .expect("sixteen letters cannot tell seventeen boxes apart");
        let short = Prefix::parse(&letter.to_string()).expect("a letter is a prefix");

        let found: Vec<Address> = held.iter().map(|&id| graph.address(id)).collect();
        let Named::Many(mut answered) = graph.lookup(&short) else {
            panic!("{} is more than one box:\n{}", short, graph)
        };
        answered.sort();
        let mut wanted = found.clone();
        wanted.sort();
        assert_eq!(answered, wanted);

        let Err(TacticError::ManyBoxes { at, .. }) = run(
            &mut graph.clone(),
            &mut Derivation::default(),
            &fire_at(Aim::Box(short.clone()), Law::Fold, Direction::Forward),
        ) else {
            panic!("an ambiguous address is not a name")
        };
        assert_eq!(at, short);

        // And the whole of any one of them is: every box's own address
        // tells it from every other.
        for (id, _) in graph.live() {
            let whole = Prefix::parse(&graph.address(id).letters()).expect("an address");
            assert_eq!(graph.lookup(&whole), Named::One(id));
            let short = Prefix::parse(&graph.shortest(id)).expect("what the listing prints");
            assert_eq!(graph.lookup(&short), Named::One(id), "{}", short);
        }
    }

    /// A focus scopes anchors, and a named box is an anchor: naming one
    /// outside the region finds nothing, the same answer a query gets.
    #[test]
    fn a_focus_scopes_a_named_box_too() {
        let graph = built("push 1 push 2 add push 3 push 4 add");
        let adds: Vec<NodeId> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Add)))
            .map(|(id, _)| id)
            .collect();
        let [inside, outside] = adds[..] else {
            panic!("two adds:\n{}", graph)
        };
        // `LastImage` with an empty derivation is the empty region, so
        // this is built the way a real focus is — from what a step landed.
        let mut g = graph.clone();
        let mut deriv = Derivation::default();
        let focused = Tactic::Within(
            Region::LastImage,
            Box::new(fire_at(
                Aim::Box(named(&graph, outside)),
                Law::Fold,
                Direction::Forward,
            )),
        );
        // Nothing has landed, so the focus is empty and the box is out of
        // it — even though it is a live box the tactic could otherwise
        // name.
        assert_eq!(
            run(&mut g, &mut deriv, &focused),
            Err(TacticError::NoMatchAt {
                at: graph.address(outside),
                law: Law::Fold,
                dir: Direction::Forward,
            })
        );
        assert!(
            g.is_live(outside) && g.is_live(inside),
            "nothing ran:\n{}",
            g
        );
    }

    /// The stated introduction: `tuple-cancel` read backward is bare
    /// wires, which no search anchors, so the wires are named — one by
    /// the address a listing would print, one by boundary — and the pair
    /// goes in on them, every reader re-pointed through it.
    #[test]
    fn a_stated_introduction_puts_the_pair_on_the_named_wires() {
        let mut graph = built("not");
        let (not, _) = graph.live().next().expect("one box");
        let mut deriv = Derivation::default();
        let stated = Tactic::State {
            at: Query::new(),
            rule: Rule::TupleCancel { n: 2 },
            dir: Direction::Backward,
            readers: None,
            with: MatchSpec {
                nodes: Vec::new(),
                inputs: vec![SrcExpr::Addressed(named(&graph, not), 0), SrcExpr::Input(0)],
            },
            pick: Pick::Unique,
        };
        assert_eq!(
            run(&mut graph, &mut deriv, &stated),
            Ok(Progress::Advanced(1))
        );
        graph.check().unwrap();

        // The pair stands on the named wires, in the named order, and the
        // boundary reads through it.
        let only = |kind: &NodeKind| {
            graph
                .live()
                .find(|(_, k)| *k == kind)
                .unwrap_or_else(|| panic!("no {} in\n{}", kind, graph))
                .0
        };
        let tuple = only(&NodeKind::Op(Prim::Tuple(2)));
        let apart = only(&NodeKind::Op(Prim::Untuple(2)));
        assert_eq!(
            graph.sources(tuple),
            [Source::Port { node: not, port: 0 }, Source::Input(0)],
            "\n{}",
            graph
        );
        assert_eq!(
            graph.outputs(),
            [Source::Port {
                node: apart,
                port: 0
            }],
            "\n{}",
            graph
        );

        // And the run is a derivation like any other: it replays.
        let record: Vec<_> = deriv.steps().cloned().collect();
        let mut again = built("not");
        replay(&mut again, &record).unwrap();
        assert_eq!(again, graph, "\n{}\n{}", again, graph);
    }

    /// A `for(...)` on a stated step: the pair goes in on the named wire
    /// for the named reader alone, and the other reader keeps the very
    /// box it always read — the split no unselective step can state.
    /// `except(...)` is the same choice said from the other end.
    #[test]
    fn a_stated_introduction_can_be_for_some_readers_only() {
        use crate::kernel::graph::isomorphic;
        // One wire, read by a `not` and an `is_bool`.
        let two_readers = || {
            let mut g = Graph::empty(1);
            let not = g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
            let test = g.add(NodeKind::Op(Prim::IsBool), vec![Source::Input(0)]);
            g.close(vec![not[0], test[0]]);
            g.check().unwrap();
            g
        };
        let mut graph = two_readers();
        let not = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::Not)))
            .expect("the not")
            .0;
        let test = graph
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Op(Prim::IsBool)))
            .expect("the test")
            .0;
        let (rule, dir) = rules::boxless(Law::TupleCancel, 1).expect("a bare-wires side");
        let stated = |readers: Option<Readers>| Tactic::State {
            at: Query::new(),
            rule: rule.clone(),
            dir,
            readers,
            with: MatchSpec {
                nodes: Vec::new(),
                inputs: vec![SrcExpr::Input(0)],
            },
            pick: Pick::Unique,
        };

        let mut deriv = Derivation::default();
        let picked = stated(Some(Readers::For(vec![Reader::Box(named(&graph, not))])));
        assert_eq!(
            run(&mut graph, &mut deriv, &picked),
            Ok(Progress::Advanced(1))
        );
        graph.check().unwrap();

        // The `not` reads through the pair; the `is_bool` reads the wire.
        assert_eq!(graph.sources(test), [Source::Input(0)], "\n{}", graph);
        let mut want = Graph::empty(1);
        let tuple = want.add(NodeKind::Op(Prim::Tuple(1)), vec![Source::Input(0)]);
        let apart = want.add(NodeKind::Op(Prim::Untuple(1)), tuple);
        let through = want.add(NodeKind::Op(Prim::Not), apart);
        let direct = want.add(NodeKind::Op(Prim::IsBool), vec![Source::Input(0)]);
        want.close(vec![through[0], direct[0]]);
        assert!(isomorphic(&graph, &want), "\n{}\n{}", graph, want);

        // The run replays, selection and all.
        let record: Vec<_> = deriv.steps().cloned().collect();
        let mut again = two_readers();
        replay(&mut again, &record).unwrap();
        assert_eq!(again, graph, "\n{}\n{}", again, graph);

        // `except` of the other reader is the same statement.
        let mut other = two_readers();
        let mut deriv = Derivation::default();
        let excepted = stated(Some(Readers::Except(vec![Reader::Box(named(
            &other, test,
        ))])));
        assert_eq!(
            run(&mut other, &mut deriv, &excepted),
            Ok(Progress::Advanced(1))
        );
        assert!(isomorphic(&other, &graph), "\n{}\n{}", other, graph);

        // A reader off the wire is a loud name: boundary output 0 reads
        // the `not`'s answer, not the wire the law is stated on.
        let mut fresh = two_readers();
        let mut deriv = Derivation::default();
        assert_eq!(
            run(
                &mut fresh,
                &mut deriv,
                &stated(Some(Readers::For(vec![Reader::Output(0)])))
            ),
            Err(TacticError::ReaderOffWire {
                reader: Reader::Output(0)
            })
        );
        // An output past the boundary is its own mistake.
        assert_eq!(
            run(
                &mut fresh,
                &mut deriv,
                &stated(Some(Readers::For(vec![Reader::Output(5)])))
            ),
            Err(TacticError::NoSuchOutput { port: 5 })
        );
        // And excepting every reader leaves the step stating nothing.
        let everyone = stated(Some(Readers::Except(vec![
            Reader::Box(named(&fresh, not)),
            Reader::Box(named(&fresh, test)),
        ])));
        assert_eq!(
            run(&mut fresh, &mut deriv, &everyone),
            Err(TacticError::NobodyLeft)
        );
        assert_eq!(fresh, two_readers(), "a refusal changes nothing");
    }

    /// The other stated introduction, and the one a branch layer wants:
    /// `specialize-equal` read backward puts a **branch** on a wire —
    /// the test of it against a second wire, answering with that second
    /// where the test held and with the wire itself where it did not.
    ///
    /// Bare on that side for the same reason `tuple-cancel` is: the
    /// answer is the wire, there is no box to anchor a search on, and the
    /// operand it is tested against is named rather than found.
    #[test]
    fn a_stated_introduction_puts_a_branch_on_a_named_wire() {
        let mut graph = built("not");
        let (not, _) = graph.live().next().expect("one box");
        let mut deriv = Derivation::default();
        let (rule, dir) = rules::boxless(Law::SpecializeEqual, 2).expect("a bare-wires side");
        let stated = Tactic::State {
            at: Query::new(),
            rule,
            dir,
            readers: None,
            with: MatchSpec {
                nodes: Vec::new(),
                inputs: vec![SrcExpr::Addressed(named(&graph, not), 0), SrcExpr::Input(0)],
            },
            pick: Pick::Unique,
        };
        assert_eq!(
            run(&mut graph, &mut deriv, &stated),
            Ok(Progress::Advanced(1))
        );
        graph.check().unwrap();

        // The test reads the wires in the order they were named, the
        // branch turns on it, and the boundary reads through the branch:
        // then block the second wire, else block the first.
        let only = |kind: &NodeKind| {
            graph
                .live()
                .find(|(_, k)| *k == kind)
                .unwrap_or_else(|| panic!("no {} in\n{}", kind, graph))
                .0
        };
        let negated = Source::Port { node: not, port: 0 };
        let test = only(&NodeKind::Op(Prim::Equal));
        assert_eq!(
            graph.sources(test),
            [negated, Source::Input(0)],
            "\n{}",
            graph
        );
        let branch = only(&NodeKind::Select);
        assert_eq!(
            graph.sources(branch),
            [
                Source::Port {
                    node: test,
                    port: 0
                },
                Source::Input(0),
                negated
            ],
            "\n{}",
            graph
        );
        assert_eq!(
            graph.outputs(),
            [Source::Port {
                node: branch,
                port: 0
            }],
            "\n{}",
            graph
        );

        // And the branch layer takes it straight back out, which is the
        // row read the way a driver reads it.
        let mut back = Derivation::default();
        run(&mut graph, &mut back, &branch_pass()).unwrap();
        graph.check().unwrap();
        assert_eq!(graph, built("not"), "\n{}", graph);

        // The run is a derivation like any other: it replays.
        let mut again = built("not");
        let record: Vec<_> = deriv.steps().cloned().collect();
        replay(&mut again, &record).unwrap();
        assert!(again.live().any(|(_, k)| matches!(k, NodeKind::Select)));
    }

    /// A stated wire fails by name, the discipline `at` keeps: a box
    /// nothing answers to, a port the box lacks, and one wire stated as
    /// two of the pattern's — which is one question answered two ways,
    /// refused where every wrong claim is.
    #[test]
    fn a_stated_wire_fails_by_name() {
        let graph = built("not");
        let (not, _) = graph.live().next().expect("one box");
        let stated = |inputs: Vec<SrcExpr>| Tactic::State {
            at: Query::new(),
            rule: Rule::TupleCancel { n: 2 },
            dir: Direction::Backward,
            readers: None,
            with: MatchSpec {
                nodes: Vec::new(),
                inputs,
            },
            pick: Pick::Unique,
        };
        let try_on = |inputs: Vec<SrcExpr>| {
            run(
                &mut graph.clone(),
                &mut Derivation::default(),
                &stated(inputs),
            )
        };

        let ghost = Prefix::parse("zzzzzzzzzzzz").expect("an address of nought");
        assert_eq!(
            try_on(vec![
                SrcExpr::Addressed(ghost.clone(), 0),
                SrcExpr::Input(0)
            ]),
            Err(TacticError::NoSuchBox { at: ghost })
        );
        let name = named(&graph, not);
        assert_eq!(
            try_on(vec![SrcExpr::Addressed(name.clone(), 1), SrcExpr::Input(0)]),
            Err(TacticError::NoSuchPort { at: name, port: 1 })
        );
        assert!(matches!(
            try_on(vec![SrcExpr::Input(0), SrcExpr::Input(0)]),
            Err(TacticError::Refused(_))
        ));
    }
}
