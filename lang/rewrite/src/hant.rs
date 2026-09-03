//! The `.hant` file: proofs, written as strategies.
//!
//! An identity states a claim; the `.hant` beside the `.hana` says how to
//! discharge it. An identity with no entry gets the default — `diagram`,
//! the decision procedure alone — so the file holds exactly the proofs that
//! need a human's direction and nothing else:
//!
//! ```text
//! // identities.hant
//! proof identities::testing_a_test_by_name = inline diagram;
//! ```
//!
//! A strategy is a run of steps, juxtaposed, acting on **one goal** — two
//! [graphs](crate::kernel::graph) of one arity, claimed to be the same program.
//! The manipulations transform it; a splitter replaces it with independent
//! subgoals, each carrying its own strategy; `diagram` closes it, and a
//! goal whose sides have become one diagram — isomorphic — closes on its
//! own:
//!
//! | step | does | fails when |
//! |---|---|---|
//! | `lhs(tactic)` | runs a graph tactic (see below) on the left side | the tactic fails — and the residual is the goal as it now stands, the last step that landed still standing |
//! | `rhs(tactic)` | the same on the right | likewise |
//! | `both(tactic)` | the same on each side in turn | likewise |
//! | `lhs(by name)` | spends another identity where its left side occurs on this one — that identity's **own proof**, carried in | the named claim is not proved, its proof is not a run on one side, or its left side does not occur here |
//! | `inline` | opens every call in both graphs, all the way down | there are no calls |
//! | `inline(name)` | opens the calls to that one sentence | it is not called here |
//! | `symm` | swaps the two sides | never — but two in a row are refused |
//! | `exact` | claims the sides are one diagram — **isomorphic** — which the auto-close has already checked, so a reached `exact` fails and shows the goal exactly as it stands | always, when reached |
//! | `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B`, the waypoint built as a graph | the waypoint's net stack change is not the goal's, or a side fails |
//! | `select-same (then: s, else: s)` | **splits a branch**: the left side answers with a `select`, so `select(c, T, E) = B` splits into the goals `T = B` and `E = B`, each on its own road. The law of that name is what puts them back together — a branch answering `B` either way *is* `B` — and the condition goes with the branch. The mirror of `cases`: that one makes a branch to reason under, this one spends the one a goal already has | the left side's answer is not one `select` — every boundary output that box's own — or a block fails, and the residual says which block |
//! | `cases(#nk)` | **case analysis** on the wire that box answers with: the instruction set promises it is `true` or `false` and nothing else, so everything depending on it becomes a branch holding one copy per case, the assumption pasted in as a literal — one checked rewrite per side, simplified under each assumption by the ordinary laws | no side names that box, nothing promises its answer is a bool, or nothing depends on it |
//! | `cases(#nk) (true: s, false: s)` | the same split, with a sub-strategy per case: each runs with its rewrites scoped to its side of the fresh branch — the hypothesis, spent as the structure it is. An arm holds side rewrites and nested `cases`; either is omissible, and a side whose branch is already gone skips its arm quietly | the split fails, or an arm's tactic does — and the residual names whose case it stood in |
//! | `diagram` | rewrites both sides by the whole table to fixpoint; they land on one diagram — isomorphic — or they do not | they do not — and the residual is both sides as the diagrams they came to |
//!
//! `diagram`, `exact`, `via` and `select-same` end a strategy — the goal is
//! closed or split, and what follows a split is written *inside* it, since
//! the subgoals are independent. A chain is nested cuts — `via { c1 } (right:
//! via { c2 })` — and each link may take a different road. A strategy that
//! ends on a manipulation is allowed: it closes only if the goal has
//! become one diagram, and says so otherwise.
//!
//! ## Citing one claim in another
//!
//! `lhs(by identities::a_lemma)` is how a proof uses a proof. The
//! identity named has a certified run of its own — the steps that take
//! its left side onto its right — and a `by` **carries that run in**:
//! the claim's left side is found here, and the run is re-applied through
//! the embedding of that occurrence ([`transplant`](crate::kernel::rules::transplant)),
//! step by step, in this goal's coordinates. What lands is a run of the
//! same ordinary rewrites, and the kernel cannot tell a `by` from a
//! `lhs(…)` that happened to spend the same steps.
//!
//! So a citation is not a shortcut, and nothing is taken on trust: what a
//! citation *means* is what every use pays for. What it needs of the
//! corpus is order — the claim has to be **proved before this one**,
//! which the corpus arranges, and two claims that lean on each other are
//! refused by name rather than ordered away. The first embedding is the
//! one spent, in the sweep's own order — the same order `fire` takes its
//! proposal in.
//!
//! ```text
//! proof identities::a_double_negative_is_the_branch_it_makes =
//!     lhs(fire(not-not)) lhs(fire(as-bool-branch));
//!
//! proof identities::three_negatives_are_a_branch_and_a_negative =
//!     lhs(by identities::a_double_negative_is_the_branch_it_makes);
//! ```
//!
//! **Any closed claim may be cited** — however it closed. A lemma proved
//! by a cut, by opening a call, by a `select-same`, or by driving both
//! sides together is as citable as one driven from the left, because
//! every close is a flat run by the time it is certified
//! ([`crate::proof::flatten`]), and a flat run is what a citation
//! carries.
//!
//! ## The tactic language, embedded
//!
//! Inside `lhs(…)`, `rhs(…)` and `both(…)` is the rewrite language of
//! [`crate::tactic`], juxtaposed like steps are:
//!
//! | tactic | is |
//! |---|---|
//! | `saturate` | the structural laws to fixpoint — the resurrected driver |
//! | `saturate(law, …)` | those laws to fixpoint |
//! | `branches` | the branch layer with its cleanup, to fixpoint |
//! | `decide` | the whole table to fixpoint — what the `diagram` closer drives |
//! | `tree` | `select-hoist` past everything but another branch, then `cond-hoist` out of every condition — the decision tree |
//! | `fire(law, …)` | the first proposal of those laws, once — fails finding none |
//! | `at(#box, law)` | that law, once, in a match that holds **that box** — the address the residual printed |
//! | `at(#box, law, backward)` | the same, reading the law's equation right to left |
//! | `on(#wire …, law)` | that law stated onto named wires — the introduction whose bare side no search anchors |
//! | `…, for(#reader …)` / `…, except(#reader …)` | on an `at` or an `on`: only the named readers follow the law — or all but them |
//! | `repeat(t …)` | the sequence until it stops advancing |
//! | `try(t …)` | the sequence, or nothing — failure becomes no progress |
//!
//! A law is named as the docs name it — `fold`, `select-same`,
//! `not-not`, the spellings [`Law::name`] holds — and `branching` names
//! the one driven list of [`crate::kernel::rules`] with a name of its
//! own. This
//! surface is smaller than the language underneath today: queries and
//! stated backward steps exist as data first, and grow a spelling here
//! when a proof wants one.
//!
//! Everywhere commas separate — a law list, an `at`'s or an `on`'s
//! fields, a `via`'s or a `cases`'s sides — **the last one is optional**:
//!
//! ```text
//! proof identities::the_long_one = lhs(saturate(
//!     fold,
//!     not-not,
//! )) diagram;
//! ```
//!
//! so a list written down the page gains a line without touching the one
//! above it, and the line a proof adds reads like the lines already there.
//! One separator is spared, and only at the end: a gap between two commas
//! names nothing, and each list says so in its own words.
//!
//! ## Saying nothing
//!
//! **Steps are juxtaposed, and no steps is a run of none.** `lhs()` is
//! the tactic that leaves its side as it stands, and `proof p = ;` the
//! strategy that runs nothing at all — the goal closes if its sides are
//! already one diagram, and says it is still open if they are not, which
//! is what the prover has always done with a strategy that ran out. So
//! commenting a proof's steps out leaves a proof that reports where the
//! goal stands, rather than a file that will not parse:
//!
//! ```text
//! proof identities::the_one_being_worked_on =
//!     lhs(decide)
//!     lhs(
//!         // at(#nkz, select-same)
//!     )
//!     diagram;
//! ```
//!
//! An arm written empty is a run of none too, and so is *not* an arm left
//! out: an omitted `via` side gets `diagram`, and `(left: )` gets nothing.
//!
//! A list is the other way round, and for the reason the two differ:
//! juxtaposing no tactics is a run of no tactics, but `fire()` names no
//! law to fire, `inline()` no sentence to open and `for()` no reader to
//! send — each an argument missing rather than a run of none, and each
//! still says so.
//!
//! ## Pointing at a box
//!
//! `fire` takes the first match it is offered anywhere on the side. `at`
//! is for when that is the wrong one: it names the box, by the address the
//! **residual listing** printed beside it, and fires the law in a match
//! that holds that box — anywhere in the match, not only where the law's
//! pattern happens to anchor. A goal with nine `fold`s available and one
//! that matters is what it is for.
//!
//! ```text
//! proof identities::the_awkward_one =
//!     lhs(decide) lhs(at(#nkz, select-same)) lhs(decide) diagram;
//! ```
//!
//! The third field is the direction, `forward` when it is left out:
//! `at(#nkz, select-same, backward)` reads the law's equation right to
//! left, which is how a proof says "put this back". Backward finds
//! something only where the law's right-hand side names enough boxes to
//! be looked for, and where the payload is one this graph's own boxes
//! spell — a right-hand side that is bare wiring pins nothing, and `on`
//! is how a proof states one of those instead of searching for it. Both
//! failures say so by name.
//!
//! ## Pointing at wires
//!
//! `on(#nk in0, tuple-cancel)` states what no search can find: the law's
//! **bare-wires side** is the pattern, so the wires are named outright —
//! `#nk` a box's answer by the address the listing printed, `#nk.1` a
//! later port, `in0` a boundary input — and the law's window goes in *on*
//! them. Every reader of each wire, the goal boundary included, comes to
//! read through the introduced pair, and the order is the window's shape:
//! `on(in1 in0, tuple-cancel)` builds the other tuple. The direction is
//! the law's own — `tuple-cancel`'s bare side is its right, so the
//! equation reads backward — and writing `backward` out is allowed and
//! checked rather than obeyed. Stated on wires the pair already cancels,
//! the step **compounds**: a second trip stacks on the first, a true
//! thing said one layer deeper, and never an error — so a `repeat` around
//! an `on` is the author claiming what a `repeat` always claims.
//!
//! `on(#nk in0, specialize-equal)` is the other one, and what it puts in
//! is a **branch**: the first wire tested against the second, answering
//! with the second where the test held and with the first where it did
//! not — which is the first wire either way, and why the answer side is
//! bare. Two wires exactly, and the order is the window's shape here
//! too: it is the wire named first that every reader comes to read the
//! branch for, and the test reads them in the order they are named.
//! [`rules::boxless`] is the table of laws `on` can state, and a law
//! whose bare side would take more payload than a width is not yet on it.
//!
//! ## Pointing at readers
//!
//! "Every reader" has one stated exception: a `for(…)` or `except(…)`
//! clause, on an `at` or an `on` alike, says **which** of the wires'
//! readers follow the law — `for` names the ones that do, `except` the
//! ones that keep the wire they have, and the rest is what a rewrite
//! always did. A reader is a box by address or `outN` for a boundary
//! output, and each must actually read a wire the law leaves, or the step
//! fails naming it. The choice travels inside the recorded match and is
//! checked reader by reader, so `on(in0, tuple-cancel, for(#nk))` sends
//! the pair in for `#nk` alone while `#qm` and the boundary go on reading
//! the wire — the split no unselective step can state. Like a `cases`
//! split, the clause covers the readers the wires have when it fires: an
//! `except`ed name is spent against that moment, not held against readers
//! a later step creates.
//!
//! An address is a box's **name**: a digest of what it computes and of
//! what that is computed from, written in letters, and the same letters
//! wherever that computation is written — the goal's other side included.
//! It is the one way this language says *where*: an `at`'s box, a stated
//! wire, a `for(…)`'s reader and a `cases`'s wire are all written the
//! same, and the last of those is why one address covers both sides of a
//! goal at once — a test written twice is one name, so a split says which
//! wire once and every side that computes it splits there.
//! A proof writes as much of one as the listing emphasised, which is as
//! much as tells that box from the others on the page, and the rest is
//! the listing's to print and the reader's to skim. What it costs is that
//! a rewrite *under* a box renames it, since a value made of different
//! values is a different value; so an `at` written off a report is good
//! for as long as the steps in front of it leave its box computing what
//! it computed. What it buys is that no other spelling of "that one"
//! exists — the listing is keyed by address precisely so a next step can
//! name what the report named. A proof whose named box is gone fails
//! loudly, naming it, rather than firing somewhere else; so does one
//! whose prefix has come to mean two boxes, and it says which.
//!
//! `inline` and `cases` are the steps that *change what is provable* — no
//! closer opens a call or invents a case analysis on its own — and the
//! tactics change what the *report* shows: a goal rewritten toward its
//! other side fails closer to the difference. `symm` moves which side the asymmetric steps read — a
//! `via`'s halves and the tactic steps are named for their sides — so it
//! is how a proof says "the interesting side is the other one" without
//! restating the identity backwards.
//!
//! An omitted `via` side gets `diagram`, because handing the decision
//! procedure the halves is what a cut is *for*; an omitted `select-same`
//! block gets it for the same reason, and a block that is already the
//! right side closes before any step runs.
//!
//! `peel` and `descend` are retired, not aliased. Both read the goal as
//! a term — a compose spine to strip, a branch node to descend into — and a graph
//! goal has neither: what they narrowed for the report, the listing does
//! by writing a branch as the block it is, and what `descend` proved arm
//! by arm is the branch layer's to rewrite. A proof that names them fails
//! loudly.
//!
//! Entries are checked both ways: an entry naming no stated identity is an
//! error (a renamed identity would otherwise silently shed its proof), and a claim
//! discharged twice was discharged once too often.
//!
//! A body — a `via` waypoint — is a **term**, in the language
//! [`crate::kernel::term`] prints and [`crate::parse`] reads, rather than in
//! Hana's: it says what it means, and a residual's boxes are written in
//! the same vocabulary. `call name` names a sentence, and
//! nothing pads — `id(k) * A` is written where a Hana sentence would have
//! inferred it.

use std::fmt;

use bytecode::{IdentityIndex, SentenceIndex};

use crate::kernel::graph::{Direction, Prefix};
use crate::kernel::rules::{self, Law};
use crate::kernel::term::TermIndex;
use crate::query::Query;
use crate::tactic::{self, Aim, MatchSpec, Pick, Reader, Readers, SrcExpr, Tactic, Wire};

/// Which side of the goal a graph tactic acts on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OnSide {
    Lhs,
    Rhs,
    Both,
}

impl OnSide {
    /// The word the surface spells it with, which is also how a proof's
    /// summary names it.
    pub fn word(self) -> &'static str {
        match self {
            OnSide::Lhs => "lhs",
            OnSide::Rhs => "rhs",
            OnSide::Both => "both",
        }
    }
}

/// One step of a strategy. `V` is what a `via` carries: the body's text as
/// parsed, a [`Body`] — the term it reads as — once the library it is written
/// against exists.
#[derive(Debug, Clone, PartialEq)]
pub enum Step<V> {
    /// Rewrite both sides by the whole table to fixpoint and ask whether
    /// they landed on one diagram — isomorphic. Closes the goal or fails
    /// with a residual; every rewrite on the way is an instance of a named
    /// law checked by [`rules::apply`](crate::kernel::rules::apply), so
    /// the verdict is a derivation's worth of checked steps and one final
    /// isomorphism.
    Diagram,
    /// Run a graph tactic on one side of the goal, or on each in turn —
    /// the rewrite language of [`crate::tactic`], embedded. A
    /// manipulation, not a closer: what it leaves is a goal, and the
    /// auto-close is what notices the sides becoming one diagram. A tactic
    /// that fails leaves its side standing at the last step that landed,
    /// and the residual shows exactly that. Boxed: a tactic is by far the
    /// widest thing a step can carry.
    Rewrite { side: OnSide, tactic: Box<Tactic> },
    /// Spend another identity where it occurs: `lhs(by name)`.
    ///
    /// Not a law and not an axiom. The identity named has a certified run
    /// of its own, and what happens here is that the run's **steps** are
    /// carried into this goal — [`transplant`](crate::kernel::rules::transplant)
    /// — so what lands is a run of the same ordinary rewrites, checked the
    /// same way, in this goal's coordinates. Nothing new is trusted: a
    /// `by` records what a `lhs(…)` records and the kernel cannot tell
    /// them apart.
    ///
    /// It needs the named identity proved before this one, which is why the
    /// corpus proves in dependency order.
    By { side: OnSide, of: V },
    /// Open calls on both sides, in place in the graphs: every one, all
    /// the way down, or — with a label — only the calls to the sentence it
    /// names, whose own calls stay closed. Recursion is forbidden, so one
    /// pass opens every instance.
    Inline(Option<V>),
    /// Swap the two sides. Equality is symmetric, so the claim is untouched;
    /// what moves is which side the asymmetric steps read.
    Symm,
    /// Claim the two sides are one diagram — isomorphic. The auto-close
    /// tests exactly that before every step, so a reached `exact` is a
    /// failed claim, and its whole job is the report: the goal exactly as
    /// it stands, with nothing normalized away — the way to *see* one.
    /// `exact` alone shows the identity as built and aligned, and after a
    /// manipulation it shows what the manipulation left.
    Exact,
    /// Cut the goal at a waypoint: `A = B` splits into the two independent
    /// goals `A = C` (left) and `C = B` (right), each discharged by its own
    /// strategy. An omitted side gets the default, `diagram`.
    Via {
        waypoint: V,
        left: Option<Strategy<V>>,
        right: Option<Strategy<V>>,
    },
    /// Case analysis on the wire one **addressed** box answers with. The
    /// box named has to be one the instruction set
    /// [guarantees answers a bool](bytecode::Instruction::yields_bool),
    /// so its answer is `true` or `false` and nothing else — and
    /// everything that depends on that answer can be replaced by a branch
    /// holding one copy of it per case, the assumed answer pasted in as a
    /// literal. That replacement is three ordinary equations (the
    /// promise written down, the coercion unpacked, and the branch grown
    /// forward over the region — see
    /// [`case_split`](crate::kernel::rules::case_split)), and this step
    /// spends them once per side that names the box — each rewrite an
    /// [`apply`](crate::kernel::rules::apply)-checked rewrite like any
    /// other, so the step itself is untrusted convenience that only picks
    /// where. The promise is the kernel's to ask for, and it asks at the
    /// wire rather than at a spelling: a box nothing promises a bool of
    /// simply offers no second case, and the step says so. The ordinary
    /// laws then simplify each copy under its assumption, and when both
    /// come out alike the introduced branch collapses as well. A
    /// manipulation, not a closer: what it leaves is a goal.
    ///
    /// `at` is under the address discipline every other *where* in this
    /// language is under — as much of a box's name as tells it from the
    /// others on the page, resolved against the live boxes at every entry
    /// ([`Graph::lookup`](crate::kernel::graph::Graph::lookup)), failing
    /// by name rather than splitting somewhere else. The listing a stuck
    /// goal prints is keyed by address, so the wire to split on is read
    /// off the report the same way an `at`'s box is: put an `exact` where
    /// the split belongs and the failure names every wire on offer.
    /// Nothing here describes the *test* — which operation, against
    /// which literal — because a description can only reach the tests it
    /// has words for, and every other step of this language had already
    /// stopped needing words for them.
    ///
    /// One address covers both sides at once, since an address is a fact
    /// about a computation rather than about a graph: a side that does
    /// not compute the box is left standing, the way a side without the
    /// test always was.
    ///
    /// The arms, when written, are per-case sub-strategies: after the
    /// split, `then_arm` runs with its rewrites scoped to the then side of
    /// the fresh branch on each side of the goal that split, and
    /// `else_arm` to the else side — the hypothesis ("the answer was
    /// true") spent as the structure it is, rather than as a context the
    /// checker would have to know about. An arm holds side rewrites and nested
    /// `cases` and nothing else, so everything it lands is ordinary
    /// checked steps in the same record as the split; the goal is closed
    /// outside the split, by whatever follows.
    Cases {
        at: Prefix,
        then_arm: Option<Strategy<V>>,
        else_arm: Option<Strategy<V>>,
    },
    /// Split the goal at the branch its **left side answers with**:
    /// `select(c, T, E) = B` becomes the two goals `T = B` and `E = B`,
    /// each discharged by its own strategy, and an omitted one gets the
    /// default.
    ///
    /// The step is named for the law that licenses it. A branch whose
    /// blocks are both `B` is `B` — [`Law::SelectSame`] — so showing each
    /// block equal to the right side shows the branch equal to it, and the
    /// condition falls away with the branch, discarded the way every
    /// untaken arm is.
    ///
    /// Where `cases` *introduces* a branch to reason under, this
    /// *eliminates* one the goal already holds: the proof stops having to
    /// find one rewriting that suits both blocks and answers for each on
    /// its own. It asks the left side to answer with one `select` and
    /// nothing else — every boundary output that box's own — and `symm` is
    /// how a proof says the branch is on the other side.
    SelectSame {
        then_arm: Option<Strategy<V>>,
        else_arm: Option<Strategy<V>>,
    },
}

/// What a step's payload reads as, once the library it names things against
/// exists: a term, or a sentence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Body {
    /// A `via` waypoint: the term it reads as, in the context the proof is
    /// being run against.
    Stone(TermIndex),
    /// An `inline` label: the one sentence it opens.
    Target(SentenceIndex),
    /// A `by` name: the one identity it spends.
    Lemma(IdentityIndex),
}

/// A strategy: steps in order, manipulations first, at most one closer last.
pub type Strategy<V> = Vec<Step<V>>;

/// A parsed `.hant` entry: which identity, and how to prove it.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofEntry {
    pub identity: String,
    pub strategy: Strategy<String>,
}

/// The default for an identity with no entry: the decision procedure alone.
pub fn default_strategy<V>() -> Strategy<V> {
    vec![Step::Diagram]
}

impl<V> fmt::Display for Step<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Step::Diagram => write!(f, "diagram"),
            Step::Rewrite { side, .. } => write!(f, "{}(…)", side.word()),
            Step::By { side, .. } => write!(f, "{}(by …)", side.word()),
            Step::Inline(None) => write!(f, "inline"),
            Step::Inline(Some(_)) => write!(f, "inline(…)"),
            Step::Symm => write!(f, "symm"),
            Step::Exact => write!(f, "exact"),
            Step::Via { .. } => write!(f, "via {{ … }}"),
            Step::Cases {
                at,
                then_arm: None,
                else_arm: None,
            } => write!(f, "cases({})", at),
            Step::Cases { at, .. } => write!(f, "cases({}) (…)", at),
            Step::SelectSame {
                then_arm: None,
                else_arm: None,
            } => write!(f, "select-same"),
            Step::SelectSame { .. } => write!(f, "select-same (…)"),
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
///
/// **No steps is a run of no steps**, which the prover already means
/// something by: a goal whose sides are one diagram closes before any step
/// runs, and one whose sides are not says the strategy ended with it still
/// open. So an empty strategy is written rather than refused, and a proof
/// whose steps are all commented out says what it has become instead of
/// failing to parse.
fn parse_strategy(input: &str) -> Result<(Strategy<String>, &str), String> {
    let mut rest = input.trim_start();
    let mut steps = Vec::new();
    while !rest.is_empty() && !rest.starts_with([';', ',', ')']) {
        let (step, after) = parse_step(rest)?;
        steps.push(step);
        rest = after.trim_start();
    }
    Ok((steps, rest))
}

fn parse_step(input: &str) -> Result<(Step<String>, &str), String> {
    // A hyphen is part of the word: `select-same` is named for the law it
    // spends, and the laws are spelled with hyphens.
    let word_len = input
        .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '-'))
        .unwrap_or(input.len());
    let (word, rest) = input.split_at(word_len);
    match word {
        "diagram" => Ok((Step::Diagram, rest)),
        "lhs" | "rhs" | "both" => {
            let side = match word {
                "lhs" => OnSide::Lhs,
                "rhs" => OnSide::Rhs,
                _ => OnSide::Both,
            };
            let (inside, after) = paren_block(rest.trim_start())
                .ok_or_else(|| format!("`{}` expects a parenthesized tactic", word))?;
            // `by` is the one thing inside a side that is not a tactic: it
            // spends a whole identity rather than a law, and what it needs —
            // that identity's own proof — is the prover's to look up, not the
            // rewrite language's. So it is dispatched here, on the head word,
            // and the surface stays `lhs(…)` either way.
            if let Some(name) = inside.trim().strip_prefix("by")
                && name.starts_with(|c: char| c.is_whitespace())
            {
                let name = name.trim();
                if name.is_empty() {
                    return Err(format!("`{}(by …)` names no identity", word));
                }
                return Ok((
                    Step::By {
                        side,
                        of: name.to_string(),
                    },
                    after,
                ));
            }
            let tactic = parse_tactics(inside).map_err(|e| format!("`{}`: {}", word, e))?;
            Ok((
                Step::Rewrite {
                    side,
                    tactic: Box::new(tactic),
                },
                after,
            ))
        }
        "inline" => {
            // A label goes in parentheses, so `inline diagram` stays two
            // steps rather than an inline of a sentence called `diagram`.
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
        // The blocks of the branch the left side answers with, each against
        // the right side. The arms ride `via`'s spelling, and their labels
        // are the graph layer's own names for a `select`'s two blocks.
        "select-same" => {
            let (arms, after) = if rest.trim_start().starts_with('(') {
                parse_arms("select-same", "then", "else", rest.trim_start())?
            } else {
                ((None, None), rest)
            };
            Ok((
                Step::SelectSame {
                    then_arm: arms.0,
                    else_arm: arms.1,
                },
                after,
            ))
        }
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
        "cases" => {
            let (inside, after) =
                paren_block(rest.trim_start()).ok_or("`cases` expects `(#address)`")?;
            let inside = inside.trim();
            if inside.is_empty() {
                return Err("`cases()` names no wire to split on".to_string());
            }
            // The wire, named the way every other *where* in this language
            // is: as much of the box's address as the listing emphasised.
            let at = Prefix::parse(inside).map_err(|e| format!("`cases`: {}", e))?;
            // The arms, when written, ride the same spelling as `via`'s
            // sides: parenthesized, labelled, either omissible.
            let (arms, after) = if after.trim_start().starts_with('(') {
                parse_arms("cases", "true", "false", after.trim_start())?
            } else {
                ((None, None), after)
            };
            Ok((
                Step::Cases {
                    at,
                    then_arm: arms.0,
                    else_arm: arms.1,
                },
                after,
            ))
        }
        "" => Err(format!("expected a step, found: {}", head_of(input))),
        other => Err(format!("no step is called `{}`", other)),
    }
}

// ---- the embedded tactic language -------------------------------------------

/// The whole of a `lhs(…)` block as one tactic; anything left over is a
/// mistake in the proof, said where it is written.
fn parse_tactics(input: &str) -> Result<Tactic, String> {
    let (tactic, rest) = parse_tactic_seq(input)?;
    let rest = rest.trim_start();
    if !rest.is_empty() {
        return Err(format!("expected a tactic, found: {}", head_of(rest)));
    }
    Ok(tactic)
}

/// Tactics by juxtaposition — a sequence, or the one tactic it holds.
///
/// The sequence may be empty, and then it is the tactic that does
/// nothing: `lhs()` leaves its side exactly as it stands, succeeding
/// without landing a rewrite, which is what a `Seq` of nothing already
/// meant to [`tactic::run`]. It is the step a proof has while what it is
/// going to say is commented out.
fn parse_tactic_seq(input: &str) -> Result<(Tactic, &str), String> {
    let mut rest = input.trim_start();
    let mut steps = Vec::new();
    while !rest.is_empty() && !rest.starts_with([',', ')']) {
        let (tactic, after) = parse_tactic(rest)?;
        steps.push(tactic);
        rest = after.trim_start();
    }
    match steps.len() {
        0 => Ok((Tactic::Seq(Vec::new()), rest)),
        1 => Ok((steps.pop().expect("one"), rest)),
        _ => Ok((Tactic::Seq(steps), rest)),
    }
}

fn parse_tactic(input: &str) -> Result<(Tactic, &str), String> {
    let word_len = input
        .find(|c: char| !(c.is_alphanumeric() || c == '_'))
        .unwrap_or(input.len());
    let (word, rest) = input.split_at(word_len);
    match word {
        // Named laws to fixpoint. The laws have to be named: there is no
        // bare `saturate`, because there is no list a driver may spend
        // without a proof having chosen it.
        "saturate" => {
            let after = rest
                .trim_start()
                .strip_prefix('(')
                .ok_or("`saturate` expects `(law, …)`")?;
            let (inside, after) = after.split_once(')').ok_or("`saturate(` never closes")?;
            let laws = parse_laws(inside)?;
            Ok((
                Tactic::Repeat(Box::new(tactic::fire_first(laws)), None),
                after,
            ))
        }
        // The one address that is a name rather than a description: a
        // box id, copied off the residual listing that printed it.
        "at" => {
            let (inside, after) = paren_block(rest.trim_start())
                .ok_or("`at` expects `(#box, law)` or `(selects-on(#wire), law, backward)`")?;
            Ok((parse_at(inside)?, after))
        }
        // The introduction: a law stated onto named wires, where no
        // search could anchor.
        "on" => {
            let (inside, after) = paren_block(rest.trim_start())
                .ok_or("`on` expects `(#wire …, law)` or `(#wire …, law, backward)`")?;
            Ok((parse_on(inside)?, after))
        }
        "branches" => Ok((tactic::branch_pass(), rest)),
        "decide" => Ok((tactic::decide(), rest)),
        // The decision tree: every branch grown forward over everything
        // but another branch, until the selects are all at the output.
        "tree" => Ok((tactic::tree(), rest)),
        "fire" => {
            let after = rest
                .trim_start()
                .strip_prefix('(')
                .ok_or("`fire` expects `(law, …)`")?;
            let (inside, after) = after.split_once(')').ok_or("`fire(` never closes")?;
            Ok((tactic::fire_first(parse_laws(inside)?), after))
        }
        "repeat" => {
            let (inside, after) =
                paren_block(rest.trim_start()).ok_or("`repeat` expects a parenthesized tactic")?;
            let (body, leftover) = parse_tactic_seq(inside)?;
            if !leftover.trim().is_empty() {
                return Err(format!("`repeat`: found: {}", head_of(leftover)));
            }
            Ok((Tactic::Repeat(Box::new(body), None), after))
        }
        "try" => {
            let (inside, after) =
                paren_block(rest.trim_start()).ok_or("`try` expects a parenthesized tactic")?;
            let (body, leftover) = parse_tactic_seq(inside)?;
            if !leftover.trim().is_empty() {
                return Err(format!("`try`: found: {}", head_of(leftover)));
            }
            Ok((Tactic::Try(Box::new(body)), after))
        }
        "" => Err(format!("expected a tactic, found: {}", head_of(input))),
        other => Err(format!("no tactic is called `{}`", other)),
    }
}

/// `at(#nkz, fold)`, `at(#nkz, not-not, backward)`: a box named by as much
/// of its address as tells it from the others, one law, and which way
/// round to read its equation — and, where a proof wants the law spent
/// for some readers only, a `for(…)`/`except(…)` clause naming them.
///
/// The `#` is the listing's own spelling and is optional here, so a
/// pasted `#nkz` and a typed `nkz` are the same box. Any prefix will do
/// while it names one box of the side the step runs on; the listing
/// emphasises exactly how much of each address that is, and a prefix that
/// grew ambiguous says so at the step rather than firing somewhere else.
/// A law **list** is refused: pointing at one box is a claim about one
/// rewrite, and `structural` there would mean "whichever of twelve laws
/// happens to fire", which is the opposite of what naming a box is for.
fn parse_at(inside: &str) -> Result<Tactic, String> {
    let mut fields = spare_last_comma(inside).split(',').map(str::trim);
    let aim = fields
        .next()
        .filter(|f| !f.is_empty())
        .ok_or("`at` names nothing to fire at")?;
    let aim = parse_aim(aim)?;
    let law = fields.next().map(str::trim).unwrap_or("");
    let law = one_law(law)?;
    let mut dir = None;
    let mut readers = None;
    for field in fields {
        match field {
            "forward" | "backward" => {
                if dir.is_some() {
                    return Err("`at` takes one direction".to_string());
                }
                dir = Some(if field == "backward" {
                    Direction::Backward
                } else {
                    Direction::Forward
                });
            }
            _ => match parse_readers(field)? {
                Some(clause) => {
                    if readers.is_some() {
                        return Err("`at` takes one `for(…)` or `except(…)`".to_string());
                    }
                    readers = Some(clause);
                }
                None => {
                    return Err(format!(
                        "`at`: a direction is `forward` or `backward`, a reader clause \
                         `for(…)` or `except(…)`, and found: {}",
                        head_of(field)
                    ));
                }
            },
        }
    }
    let dir = dir.unwrap_or(Direction::Forward);
    Ok(match readers {
        None => tactic::fire_at(aim, law, dir),
        Some(readers) => tactic::fire_at_for(aim, law, dir, readers),
    })
}

/// `for(#nk out0)` / `except(#nk)`: which readers of the wires a law
/// leaves the step is for — the rest keep the wire they have. Readers are
/// spelled the way a listing prints them: a box by address, `outN` a
/// boundary output. `None` for a field that is no reader clause at all,
/// so the caller can say what else it takes.
fn parse_readers(written: &str) -> Result<Option<Readers>, String> {
    let (keyword, rest) = if let Some(rest) = written.strip_prefix("for") {
        ("for", rest)
    } else if let Some(rest) = written.strip_prefix("except") {
        ("except", rest)
    } else {
        return Ok(None);
    };
    let inside = rest
        .trim_start()
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .ok_or_else(|| format!("`{}` expects `(#reader …)`", keyword))?
        .trim();
    if inside.is_empty() {
        return Err(format!("`{}` names no readers", keyword));
    }
    let readers: Vec<Reader> = inside
        .split_whitespace()
        .map(|reader| parse_reader(keyword, reader))
        .collect::<Result<_, _>>()?;
    Ok(Some(match keyword {
        "for" => Readers::For(readers),
        _ => Readers::Except(readers),
    }))
}

/// One reader: `out2` is boundary output 2, anything else a box by as
/// much of its address as tells it apart — the `#` optional, as
/// everywhere. Unambiguous even though the alphabet has `o`, `u` and `t`:
/// no address holds a digit, so `out1` can only be the boundary and
/// `outq` only a box.
fn parse_reader(keyword: &str, written: &str) -> Result<Reader, String> {
    if let Some(digits) = written.strip_prefix("out")
        && !digits.is_empty()
        && digits.chars().all(|c| c.is_ascii_digit())
    {
        let i = digits
            .parse()
            .map_err(|_| format!("`{}`: `{}` is past any boundary", keyword, written))?;
        return Ok(Reader::Output(i));
    }
    Ok(Reader::Box(
        Prefix::parse(written).map_err(|why| format!("`{}`: {}", keyword, why))?,
    ))
}

/// What an `at` is aimed at: `#nk` is that one box, and
/// `selects-on(#nk)` every branch turning on what it answers.
///
/// The second is a set because a branch is. A `select` carries one answer,
/// so a `branch` leaving `n` values is `n` peers on one condition — the
/// lot of which a listing draws one bracket around, and none of which is
/// the branch on its own. Writing `n` addresses for what a report shows as
/// one `if` is the thing this spares, and it spares knowing `n`.
///
/// The wire is written the way the listing prints one: `in0` for a
/// boundary input, `#nk` for output 0 of a box, `#nk.1` for a later port.
fn parse_aim(written: &str) -> Result<Aim, String> {
    let Some(rest) = written.strip_prefix("selects-on") else {
        return Ok(Aim::Box(
            Prefix::parse(written).map_err(|why| format!("`at`: {}", why))?,
        ));
    };
    let inside = rest
        .trim_start()
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .ok_or("`selects-on` expects `(#wire)`")?
        .trim();
    if inside.is_empty() {
        return Err("`selects-on` names no wire".to_string());
    }
    Ok(Aim::SelectsOn(parse_condition(inside)?))
}

/// One wire, as `at`'s aim spells it — the same alphabet [`parse_wire`]
/// reads for `on`, and a different type because there are no bindings
/// here for the other two forms of a source to have come from.
fn parse_condition(written: &str) -> Result<Wire, String> {
    if let Some(digits) = written.strip_prefix("in")
        && !digits.is_empty()
        && digits.chars().all(|c| c.is_ascii_digit())
    {
        let i = digits
            .parse()
            .map_err(|_| format!("`selects-on`: `{}` is past any boundary", written))?;
        return Ok(Wire::Input(i));
    }
    let (name, port) = match written.split_once('.') {
        Some((name, port)) => (
            name,
            port.parse::<usize>()
                .map_err(|_| format!("`selects-on`: `{}` names no port of `{}`", port, name))?,
        ),
        None => (written, 0),
    };
    let prefix = Prefix::parse(name).map_err(|why| format!("`selects-on`: {}", why))?;
    Ok(Wire::Port(prefix, port))
}

/// `on(#nk in0, tuple-cancel)`: wires named in order, and the law whose
/// **bare-wires side** they stand for — the introduction no search can
/// find, since a side with no boxes anchors nowhere. The wires are the
/// pattern, so the law's window goes in *on* them: every reader of each
/// wire, the goal boundary included, comes to read through it — unless a
/// `for(…)`/`except(…)` clause says which readers follow — and the
/// order is the window's shape — `on(in1 in0, tuple-cancel)` builds the
/// other tuple.
///
/// The direction is the law's own — `tuple-cancel`'s bare side is its
/// right, so the equation reads backward — and writing it out is allowed
/// and checked rather than obeyed. Stated on wires the pair already
/// cancels, the step compounds: a second trip stacks on the first, a true
/// thing said one layer deeper, and never an error.
fn parse_on(inside: &str) -> Result<Tactic, String> {
    let mut fields = spare_last_comma(inside).split(',').map(str::trim);
    let wires = fields
        .next()
        .filter(|f| !f.is_empty())
        .ok_or("`on` names no wires")?;
    let inputs: Vec<SrcExpr> = wires
        .split_whitespace()
        .map(parse_wire)
        .collect::<Result<_, _>>()?;
    let law = fields.next().map(str::trim).unwrap_or("");
    if law.is_empty() {
        return Err("`on` names no law".to_string());
    }
    let law = match parse_laws(law)?[..] {
        [law] => law,
        _ => {
            return Err(format!(
                "`on` states one law, and `{}` is a list of them",
                law
            ));
        }
    };
    let Some((rule, dir)) = rules::boxless(law, inputs.len()) else {
        return Err(format!(
            "`{}` has no bare-wires side to state on {} {} — `on` introduces a law \
             one side of which is wiring alone, the way `tuple-cancel`'s right side \
             is `id(n)` on any width, and `specialize-equal`'s answer is the first \
             of exactly two wires",
            law.name(),
            inputs.len(),
            if inputs.len() == 1 { "wire" } else { "wires" }
        ));
    };
    let reads = match dir {
        Direction::Forward => "forward",
        Direction::Backward => "backward",
    };
    let mut spelled = false;
    let mut readers = None;
    for field in fields {
        match field {
            word if word == reads && !spelled => spelled = true,
            "forward" | "backward" if !spelled => {
                return Err(format!(
                    "`on`: `{}`'s bare-wires side reads {}, not {}",
                    law.name(),
                    reads,
                    field
                ));
            }
            _ => match parse_readers(field)? {
                Some(clause) => {
                    if readers.is_some() {
                        return Err("`on` takes one `for(…)` or `except(…)`".to_string());
                    }
                    readers = Some(clause);
                }
                None => {
                    return Err(format!(
                        "`on`: a direction is `forward` or `backward`, a reader clause \
                         `for(…)` or `except(…)`, and found: {}",
                        head_of(field)
                    ));
                }
            },
        }
    }
    Ok(Tactic::State {
        at: Query::new(),
        rule,
        dir,
        with: MatchSpec {
            nodes: Vec::new(),
            inputs,
        },
        pick: Pick::Unique,
        readers,
    })
}

/// One wire of an `on`: `in2` is boundary input 2, `#nk` is output 0 of
/// the box that address names, and `#nk.1` a later port. The `#` is the
/// listing's own spelling and is optional, as it is in `at` — and no
/// address can begin `in`, the alphabet having no `i`.
fn parse_wire(written: &str) -> Result<SrcExpr, String> {
    if let Some(digits) = written.strip_prefix("in")
        && !digits.is_empty()
        && digits.chars().all(|c| c.is_ascii_digit())
    {
        let i = digits
            .parse()
            .map_err(|_| format!("`on`: `{}` is past any boundary", written))?;
        return Ok(SrcExpr::Input(i));
    }
    let (name, port) = match written.split_once('.') {
        Some((name, port)) => (
            name,
            port.parse::<usize>()
                .map_err(|_| format!("`on`: `{}` names no port of `{}`", port, name))?,
        ),
        None => (written, 0),
    };
    let prefix = Prefix::parse(name).map_err(|why| format!("`on`: {}", why))?;
    Ok(SrcExpr::Addressed(prefix, port))
}

/// The last comma of a list is optional — `fire(fold, not-not,)`, and an
/// `at`'s fields the same. It is what lets a list written down the page
/// gain a line without touching the one above it, which a `via`'s sides
/// have always allowed; the lists spelled with commas allow it here.
///
/// Exactly one separator is spared, and at the end: a gap between two
/// commas still names nothing, and the list says so in its own words.
fn spare_last_comma(inside: &str) -> &str {
    inside.trim_end().strip_suffix(',').unwrap_or(inside)
}

/// One law and not a list — what an address to a single box may name.
fn one_law(name: &str) -> Result<Law, String> {
    if name.is_empty() {
        return Err("`at` names no law".to_string());
    }
    match parse_laws(name)?[..] {
        [law] => Ok(law),
        _ => Err(format!(
            "`at` fires one law at one box, and `{}` is a list of them",
            name
        )),
    }
}

/// Law names as the docs spell them, and the driven list by its name.
///
/// The spellings are [`Law::name`]'s, scanned rather than restated, so the
/// surface gains a law the moment the table names one and a message that
/// names a law cannot disagree with a proof that names the same one.
fn parse_laws(inside: &str) -> Result<Vec<Law>, String> {
    let mut out = Vec::new();
    for name in spare_last_comma(inside).split(',') {
        let name = name.trim();
        out.extend(match name {
            "branching" => rules::branching(),
            "" => return Err("a law list names no law".to_string()),
            _ => match Law::every().into_iter().find(|law| law.name() == name) {
                Some(law) => vec![law],
                None => return Err(format!("no law is called `{}`", name)),
            },
        });
    }
    Ok(out)
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

/// The closers close: nothing may follow `diagram`, `exact` or `via` — a
/// split goal's remaining work is written inside the split, since the
/// subgoals are independent. Sides answer for themselves.
fn validate<V>(strategy: &Strategy<V>) -> Result<(), String> {
    for (i, step) in strategy.iter().enumerate() {
        let last = i + 1 == strategy.len();
        match step {
            Step::Diagram | Step::Exact | Step::Via { .. } | Step::SelectSame { .. } if !last => {
                return Err(format!("`{}` closes the goal; nothing can follow it", step));
            }
            Step::Via { left, right, .. } => {
                for side in [left, right].into_iter().flatten() {
                    validate(side)?;
                }
            }
            // A splitter's subgoals are goals like any other, so each arm
            // is a whole strategy — closers and all — rather than the
            // rewrites-only arm a `cases` case takes.
            Step::SelectSame { then_arm, else_arm } => {
                for block in [then_arm, else_arm].into_iter().flatten() {
                    validate(block)?;
                }
            }
            Step::Cases {
                then_arm, else_arm, ..
            } => {
                for arm in [then_arm, else_arm].into_iter().flatten() {
                    validate_arm(arm)?;
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

/// A `cases` arm holds side rewrites and nested `cases` and nothing else.
/// The restriction is the proof object's: everything an arm lands must be
/// ordinary checked steps appended to the split's own record, and the
/// steps refused here re-perform some other way — `inline` re-opens,
/// `symm` turns the goal, the closers close it — none of which has a
/// reading *inside* a branch. The goal is closed outside the split.
fn validate_arm<V>(arm: &Strategy<V>) -> Result<(), String> {
    for step in arm {
        match step {
            Step::Rewrite { .. } => {}
            Step::Cases {
                then_arm, else_arm, ..
            } => {
                for nested in [then_arm, else_arm].into_iter().flatten() {
                    validate_arm(nested)?;
                }
            }
            other => {
                return Err(format!(
                    "`{}` cannot appear inside a `cases` arm: an arm holds side \
                     rewrites and nested `cases`, and the goal is closed outside \
                     the split",
                    other
                ));
            }
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

/// The same for `( ... )` — what a tactic block sits in.
fn paren_block(text: &str) -> Option<(&str, &str)> {
    let mut chars = text.char_indices();
    let (_, '(') = chars.next()? else { return None };
    let mut depth = 1usize;
    for (i, c) in chars {
        match c {
            '(' => depth += 1,
            ')' => {
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
    /// An address as a proof writes one, which is as much of it as the
    /// listing emphasised.
    fn spelled(letters: &str) -> Prefix {
        Prefix::parse(letters).expect("a prefix of an address")
    }

    /// `by` is the one thing inside a side that is not a tactic, and it is
    /// told apart by its head word alone — so a law or a tactic whose name
    /// merely begins with those two letters is still a tactic.
    #[test]
    fn a_side_takes_a_lemma_as_well_as_a_tactic() {
        let entries = parse_hant(
            "proof identities::spends_one = lhs(by identities::a_lemma) rhs(by other) diagram;",
        )
        .unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![
                Step::By {
                    side: OnSide::Lhs,
                    of: "identities::a_lemma".to_string()
                },
                Step::By {
                    side: OnSide::Rhs,
                    of: "other".to_string()
                },
                Step::Diagram,
            ]
        );

        // A tactic still parses as one, `by`-shaped name or not.
        let entries = parse_hant("proof identities::x = both(branches);").unwrap();
        assert!(matches!(entries[0].strategy[..], [Step::Rewrite { .. }]));

        assert!(parse_hant("proof identities::x = lhs(by);").is_err());
        assert!(parse_hant("proof identities::x = lhs(by );").is_err());
    }

    #[test]
    fn a_proof_file_parses_into_its_entries() {
        let entries = parse_hant(
            r#"
            // how the hard ones close
            proof identities::by_name = inline diagram;
            proof identities::wrapped =
                symm via { drop(1) ; push true } (left: inline diagram);
            "#,
        )
        .unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].identity, "identities::by_name");
        assert_eq!(entries[0].strategy, vec![Step::Inline(None), Step::Diagram]);
        let [
            Step::Symm,
            Step::Via {
                waypoint,
                left,
                right,
            },
        ] = &entries[1].strategy[..]
        else {
            panic!("{:?}", entries[1].strategy);
        };
        assert_eq!(waypoint, "drop(1) ; push true");
        assert_eq!(
            left.as_deref(),
            Some([Step::Inline(None), Step::Diagram].as_slice())
        );
        assert!(right.is_none());
    }

    #[test]
    fn a_closer_mid_strategy_is_refused() {
        let err = parse_hant("proof p = diagram inline;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        let err = parse_hant("proof p = via { push 1 } (left: diagram inline);").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
    }

    #[test]
    fn a_tactic_block_reads_as_the_language_it_embeds() {
        use crate::tactic::{Pick, RuleSpec, Tactic};

        let entries = parse_hant("proof p = lhs(saturate(not-not)) exact;").unwrap();
        let [Step::Rewrite { side, tactic }, Step::Exact] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(*side, OnSide::Lhs);
        assert_eq!(
            tactic.as_ref(),
            &Tactic::Repeat(Box::new(tactic::fire_first(vec![Law::NotNot])), None)
        );

        let entries =
            parse_hant("proof p = both(decide branches tree try(fire(not-not))) diagram;").unwrap();
        let [Step::Rewrite { side, tactic }, Step::Diagram] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(*side, OnSide::Both);
        let Tactic::Seq(steps) = tactic.as_ref() else {
            panic!("{:?}", tactic);
        };
        assert_eq!(steps[0], tactic::decide());
        assert_eq!(steps[1], tactic::branch_pass());
        assert_eq!(steps[2], tactic::tree());
        assert_eq!(
            steps[3],
            Tactic::Try(Box::new(tactic::fire_first(vec![Law::NotNot])))
        );

        // A law list spells the docs' names, and the driven list by its.
        let entries = parse_hant("proof p = rhs(saturate(select-same, branching)) exact;").unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!();
        };
        let Tactic::Repeat(body, None) = tactic.as_ref() else {
            panic!("{:?}", tactic);
        };
        let Tactic::Fire {
            rule: RuleSpec::ReadOff { laws, .. },
            pick: Pick::First,
            ..
        } = body.as_ref()
        else {
            panic!("{:?}", body);
        };
        assert_eq!(laws, &[vec![Law::SelectSame], rules::branching()].concat());
    }

    #[test]
    fn a_case_split_parses_and_polices_its_address() {
        // A manipulation now, not a closer: the split lands inside the
        // graph, and the strategy carries on. The wire is named the way
        // every other *where* in this language is — as much of a box's
        // address as the listing emphasised.
        let entries = parse_hant("proof p = inline cases(#nkz) cases(mlk) diagram;").unwrap();
        let [
            Step::Inline(None),
            Step::Cases {
                at: first,
                then_arm: None,
                else_arm: None,
            },
            Step::Cases { at: second, .. },
            Step::Diagram,
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        // The `#` a listing prints with is accepted and dropped, so a name
        // pasted out of a report is a name.
        assert_eq!(first.letters(), "nkz");
        assert_eq!(second.letters(), "mlk");

        // And an address is held to being one: the letters an address is
        // written in, at least one of them, and no more than an address.
        let err = parse_hant("proof p = cases();").unwrap_err();
        assert!(err.contains("names no wire"), "{}", err);
        let err = parse_hant("proof p = cases(equal);").unwrap_err();
        assert!(err.contains("is not one of the letters"), "{}", err);
        let err = parse_hant("proof p = cases(#zzzzzzzzzzzzz);").unwrap_err();
        assert!(err.contains("longer than an address"), "{}", err);
    }

    #[test]
    fn a_structured_case_split_parses_its_arms() {
        // The arms ride `via`'s spelling: parenthesized, labelled, either
        // omissible — and an arm may split again, which is how a proof
        // writes a decision tree.
        let entries = parse_hant(
            "proof p = cases(#nk) (true: both(decide), \
             false: both(decide) cases(#zy) (true: both(decide))) diagram;",
        )
        .unwrap();
        let [
            Step::Cases {
                at,
                then_arm: Some(then_arm),
                else_arm: Some(else_arm),
            },
            Step::Diagram,
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(at.letters(), "nk");
        assert!(matches!(then_arm[..], [Step::Rewrite { .. }]));
        let [
            Step::Rewrite { .. },
            Step::Cases {
                then_arm: Some(nested),
                else_arm: None,
                ..
            },
        ] = &else_arm[..]
        else {
            panic!("{:?}", else_arm);
        };
        assert!(matches!(nested[..], [Step::Rewrite { .. }]));

        // An omitted pair of arms is the bare split, unchanged.
        let entries = parse_hant("proof p = cases(#nk) diagram;").unwrap();
        assert!(matches!(
            entries[0].strategy[..],
            [
                Step::Cases {
                    then_arm: None,
                    else_arm: None,
                    ..
                },
                Step::Diagram
            ]
        ));

        // A duplicated label is refused the way `via`'s is.
        let err = parse_hant("proof p = cases(#nk) (true: both(decide), true: both(decide));")
            .unwrap_err();
        assert!(err.contains("names a side twice"), "{}", err);
    }

    /// The splitter that eliminates a branch, and the one step whose name
    /// holds a hyphen — it is named for the law that licenses it.
    #[test]
    fn a_branch_splits_into_its_two_blocks() {
        let entries = parse_hant("proof p = select-same;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![Step::SelectSame {
                then_arm: None,
                else_arm: None
            }]
        );

        // The arms ride `via`'s spelling and `cases`'s labels, and either
        // is omissible — a block that is already the right side needs no
        // strategy of its own.
        let entries =
            parse_hant("proof p = symm select-same (then: inline diagram, else: exact);").unwrap();
        let [
            Step::Symm,
            Step::SelectSame {
                then_arm: Some(then_arm),
                else_arm: Some(else_arm),
            },
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(then_arm.as_slice(), [Step::Inline(None), Step::Diagram]);
        assert_eq!(else_arm.as_slice(), [Step::Exact]);

        let entries = parse_hant("proof p = select-same (else: diagram);").unwrap();
        assert!(matches!(
            entries[0].strategy[..],
            [Step::SelectSame {
                then_arm: None,
                else_arm: Some(_)
            }]
        ));

        // A splitter closes the goal, and its blocks are goals in their
        // own right — so each takes a whole strategy, closer and all.
        let err = parse_hant("proof p = select-same diagram;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        let err = parse_hant("proof p = select-same (else: diagram inline);").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        let err = parse_hant("proof p = select-same (true: diagram);").unwrap_err();
        assert!(err.contains("`then:` or `else:`"), "{}", err);
    }

    #[test]
    fn an_arm_holds_rewrites_and_splits_only() {
        // The goal is closed outside the split: everything an arm lands
        // must be checked steps in the split's own record, and the steps
        // that re-perform some other way have no reading inside a branch.
        for refused in [
            "diagram",
            "exact",
            "inline",
            "symm",
            "via { push 1 }",
            "select-same",
        ] {
            let err = parse_hant(&format!(
                "proof p = cases(#nk) (true: {}) diagram;",
                refused
            ))
            .unwrap_err();
            assert!(
                err.contains("cannot appear inside a `cases` arm"),
                "{}: {}",
                refused,
                err
            );
        }
        // Nested arms are held to the same rule.
        let err = parse_hant("proof p = cases(#nk) (true: cases(#zy) (false: inline)) diagram;")
            .unwrap_err();
        assert!(
            err.contains("cannot appear inside a `cases` arm"),
            "{}",
            err
        );
    }

    #[test]
    fn a_tactic_that_is_not_one_is_refused_where_it_is_written() {
        let err = parse_hant("proof p = lhs(flatten) exact;").unwrap_err();
        assert!(err.contains("no tactic is called `flatten`"), "{}", err);
        let err = parse_hant("proof p = lhs(fire(fold, upside-down)) exact;").unwrap_err();
        assert!(err.contains("no law is called `upside-down`"), "{}", err);
        let err = parse_hant("proof p = lhs(saturate(fold) exact;").unwrap_err();
        assert!(err.contains("parenthesized tactic"), "{}", err);
    }

    #[test]
    fn a_malformed_entry_is_refused_with_its_name() {
        let err = parse_hant("proof foo = flatten;").unwrap_err();
        assert!(err.contains("foo") && err.contains("flatten"), "{}", err);
        let err = parse_hant("prove foo = diagram;").unwrap_err();
        assert!(err.contains("expected `proof`"), "{}", err);
    }

    #[test]
    fn a_cut_closes_its_goal() {
        // Nothing follows a split: the subgoals' work is written inside it.
        let err = parse_hant("proof p = via { push 1 } diagram;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
        // A chain is nested cuts, and each side may take its own road.
        let entries =
            parse_hant("proof p = via { push 1 } (left: inline diagram, right: via { push 2 });")
                .unwrap();
        let [Step::Via { left, right, .. }] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(
            left.as_deref(),
            Some([Step::Inline(None), Step::Diagram].as_slice())
        );
        assert!(matches!(right.as_deref(), Some([Step::Via { .. }])));
    }

    #[test]
    fn an_inline_label_is_parenthesized() {
        // Parenthesized so that `inline diagram` stays two steps.
        let entries = parse_hant("proof p = inline diagram;").unwrap();
        assert_eq!(entries[0].strategy, vec![Step::Inline(None), Step::Diagram]);
        let entries = parse_hant("proof p = inline(types_test::is_tag) diagram;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![
                Step::Inline(Some("types_test::is_tag".to_string())),
                Step::Diagram
            ]
        );
        let err = parse_hant("proof p = inline() diagram;").unwrap_err();
        assert!(err.contains("names no sentence"), "{}", err);
    }

    #[test]
    fn exact_is_a_closer() {
        let entries = parse_hant("proof p = inline exact;").unwrap();
        assert_eq!(entries[0].strategy, vec![Step::Inline(None), Step::Exact]);
        let err = parse_hant("proof p = exact diagram;").unwrap_err();
        assert!(err.contains("nothing can follow"), "{}", err);
    }

    #[test]
    fn symm_parses_and_says_nothing_twice() {
        let entries = parse_hant("proof p = symm inline diagram;").unwrap();
        assert_eq!(
            entries[0].strategy,
            vec![Step::Symm, Step::Inline(None), Step::Diagram]
        );
        let err = parse_hant("proof p = symm symm diagram;").unwrap_err();
        assert!(err.contains("`symm symm`"), "{}", err);
    }

    #[test]
    fn the_retired_steps_are_unknown() {
        // The e-graph era's steps are gone, and so are the term-shaped ones
        // a graph goal has no reading for — none aliased: a proof that
        // names one should fail loudly rather than mean something else.
        for retired in ["egraph", "solve", "norm", "norm_trusted", "peel"] {
            let err = parse_hant(&format!("proof p = {};", retired)).unwrap_err();
            assert!(err.contains("no step is called"), "{}: {}", retired, err);
        }
        let err = parse_hant("proof p = descend(then: diagram);").unwrap_err();
        assert!(err.contains("no step is called"), "{}", err);
    }

    /// The address a residual hands you, read back: a box id, a law, and
    /// which way round to read the law's equation.
    #[test]
    fn a_box_can_be_named_by_the_address_the_report_printed() {
        let entries = parse_hant("proof p = lhs(at(#nkz, select-same)) diagram;").unwrap();
        let [Step::Rewrite { side, tactic }, Step::Diagram] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(*side, OnSide::Lhs);
        assert_eq!(
            tactic.as_ref(),
            &tactic::fire_at(
                Aim::Box(spelled("nkz")),
                Law::SelectSame,
                Direction::Forward
            )
        );

        // The `#` is the listing's spelling, and optional here, so a
        // pasted address and a typed one are the same box.
        let entries = parse_hant("proof p = rhs(at(nkz, select-same)) diagram;").unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!()
        };
        assert_eq!(
            tactic.as_ref(),
            &tactic::fire_at(
                Aim::Box(spelled("nkz")),
                Law::SelectSame,
                Direction::Forward
            )
        );

        // The third field is the direction, `forward` when it is left out.
        let entries = parse_hant("proof p = lhs(at(#sq, select-same, backward)) diagram;").unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!()
        };
        assert_eq!(
            tactic.as_ref(),
            &tactic::fire_at(
                Aim::Box(spelled("sq")),
                Law::SelectSame,
                Direction::Backward
            )
        );

        // And it composes like any other tactic.
        let entries =
            parse_hant("proof p = both(decide try(at(#w, not-not, backward)) decide) diagram;")
                .unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!()
        };
        let Tactic::Seq(steps) = tactic.as_ref() else {
            panic!("{:?}", tactic)
        };
        assert_eq!(
            steps[1],
            Tactic::Try(Box::new(tactic::fire_at(
                Aim::Box(spelled("w")),
                Law::NotNot,
                Direction::Backward
            )))
        );
    }

    /// `selects-on(#wire)` is the other thing an `at` can be aimed at: the
    /// branch a wire decides, which is a `select` per answer and so a set.
    /// The wire is written the way the listing prints one.
    #[test]
    fn a_branch_is_named_by_the_wire_it_turns_on() {
        for (written, want) in [
            ("in0", Wire::Input(0)),
            ("in12", Wire::Input(12)),
            ("#nkz", Wire::Port(spelled("nkz"), 0)),
            // Bare, the way `at`'s own address may be written.
            ("nkz", Wire::Port(spelled("nkz"), 0)),
            ("#nkz.2", Wire::Port(spelled("nkz"), 2)),
        ] {
            let proof = format!(
                "proof p = lhs(at(selects-on({}), select-hoist)) diagram;",
                written
            );
            let entries = parse_hant(&proof).unwrap();
            let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
                panic!("{}", proof)
            };
            assert_eq!(
                tactic.as_ref(),
                &tactic::fire_at(Aim::SelectsOn(want), Law::SelectHoist, Direction::Forward),
                "{}",
                proof
            );
        }

        // It takes a direction like any other `at`.
        let entries =
            parse_hant("proof p = lhs(at(selects-on(in0), select-same, backward)) diagram;")
                .unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!()
        };
        assert_eq!(
            tactic.as_ref(),
            &tactic::fire_at(
                Aim::SelectsOn(Wire::Input(0)),
                Law::SelectSame,
                Direction::Backward
            )
        );

        // And an aim prints the way it is written.
        assert_eq!(
            Aim::SelectsOn(Wire::Port(spelled("nkz"), 2)).to_string(),
            "selects-on(#nkz.2)"
        );
        assert_eq!(
            Aim::SelectsOn(Wire::Input(0)).to_string(),
            "selects-on(in0)"
        );
    }

    /// Every way of writing the address wrong, answered where it is
    /// written. A list of laws is refused today: naming one box is a
    /// claim about one rewrite, and `structural` there would mean
    /// "whichever of twelve happens to fire".
    #[test]
    fn a_named_box_is_written_one_way() {
        for (proof, expected) in [
            ("proof p = lhs(at) diagram;", "expects"),
            ("proof p = lhs(at()) diagram;", "names nothing to fire at"),
            ("proof p = lhs(at(#nkz)) diagram;", "names no law"),
            (
                "proof p = lhs(at(the third one, select-same)) diagram;",
                "is not one of the letters",
            ),
            (
                "proof p = lhs(at(#41, select-same)) diagram;",
                "is not one of the letters",
            ),
            (
                "proof p = lhs(at(#nkz, no-such-law)) diagram;",
                "no law is called",
            ),
            (
                "proof p = lhs(at(#nkz, branching)) diagram;",
                "is a list of them",
            ),
            (
                "proof p = lhs(at(#nkz, select-same, sideways)) diagram;",
                "forward",
            ),
            (
                "proof p = lhs(at(#nkz, select-same, backward, 9)) diagram;",
                "and found",
            ),
            // The set-valued aim, and the three ways of writing it wrong.
            (
                "proof p = lhs(at(selects-on, select-same)) diagram;",
                "expects `(#wire)`",
            ),
            (
                "proof p = lhs(at(selects-on(), select-same)) diagram;",
                "names no wire",
            ),
            (
                "proof p = lhs(at(selects-on(#nk.z), select-same)) diagram;",
                "names no port",
            ),
        ] {
            let err = parse_hant(proof).unwrap_err();
            assert!(err.contains(expected), "{}: {}", proof, err);
        }
    }

    /// `on` states a law onto named wires — the introduction the matcher
    /// cannot find — and compiles to the stated step it is.
    #[test]
    fn wires_can_be_named_and_a_law_stated_onto_them() {
        let entries = parse_hant("proof p = lhs(on(#nk in0, tuple-cancel)) diagram;").unwrap();
        let [Step::Rewrite { side, tactic }, Step::Diagram] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(*side, OnSide::Lhs);
        assert_eq!(
            tactic.as_ref(),
            &Tactic::State {
                at: Query::new(),
                rule: rules::Rule::TupleCancel { n: 2 },
                dir: Direction::Backward,
                readers: None,
                with: MatchSpec {
                    nodes: Vec::new(),
                    inputs: vec![SrcExpr::Addressed(spelled("nk"), 0), SrcExpr::Input(0)],
                },
                pick: Pick::Unique,
            }
        );

        // The other row `on` can state, and the branch it puts in: two
        // wires exactly, read backward like its neighbour.
        let entries = parse_hant("proof p = lhs(on(#nk in0, specialize-equal)) diagram;").unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(
            tactic.as_ref(),
            &Tactic::State {
                at: Query::new(),
                rule: rules::Rule::SpecializeEqual {
                    answered: rules::Side::Deep,
                },
                dir: Direction::Backward,
                readers: None,
                with: MatchSpec {
                    nodes: Vec::new(),
                    inputs: vec![SrcExpr::Addressed(spelled("nk"), 0), SrcExpr::Input(0)],
                },
                pick: Pick::Unique,
            }
        );

        // A later port, and the direction written out — allowed while it
        // is the law's own.
        let entries =
            parse_hant("proof p = rhs(on(#nk.1 in2, tuple-cancel, backward)) diagram;").unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!()
        };
        let Tactic::State { with, .. } = tactic.as_ref() else {
            panic!("{:?}", tactic)
        };
        assert_eq!(
            with.inputs,
            vec![SrcExpr::Addressed(spelled("nk"), 1), SrcExpr::Input(2)]
        );
    }

    /// Every way of writing an `on` wrong, answered where it is written —
    /// the direction included, which is the law's to say.
    #[test]
    fn a_stated_wire_is_written_one_way() {
        for (proof, expected) in [
            ("proof p = lhs(on) diagram;", "expects"),
            ("proof p = lhs(on()) diagram;", "names no wires"),
            ("proof p = lhs(on(#nk)) diagram;", "names no law"),
            (
                "proof p = lhs(on(#nk in0, fold)) diagram;",
                "has no bare-wires side",
            ),
            (
                "proof p = lhs(on(#nk, specialize-equal)) diagram;",
                "no bare-wires side to state on 1 wire",
            ),
            (
                "proof p = lhs(on(#nk in0, tuple-cancel, forward)) diagram;",
                "reads backward, not forward",
            ),
            (
                "proof p = lhs(on(#i7, tuple-cancel)) diagram;",
                "is not one of the letters",
            ),
            (
                "proof p = lhs(on(#nk.x in0, tuple-cancel)) diagram;",
                "names no port",
            ),
            (
                "proof p = lhs(on(#nk in0, branching)) diagram;",
                "is a list of them",
            ),
            (
                "proof p = lhs(on(#nk in0, tuple-cancel, sideways)) diagram;",
                "forward",
            ),
            (
                "proof p = lhs(on(#nk in0, tuple-cancel, backward, 9)) diagram;",
                "and found",
            ),
        ] {
            let err = parse_hant(proof).unwrap_err();
            assert!(err.contains(expected), "{}: {}", proof, err);
        }
    }

    /// The reader clause, parsed on `at` and `on` alike: `for(...)` names
    /// the readers that follow the law, `except(...)` the ones that keep
    /// their wire, and the readers are spelled the way a listing prints
    /// them — a box by address, `outN` a boundary output.
    #[test]
    fn a_reader_clause_is_parsed_on_at_and_on() {
        let entries =
            parse_hant("proof p = lhs(at(#nk, not-not, backward, for(#qm out0))) diagram;")
                .unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(
            tactic.as_ref(),
            &Tactic::At {
                at: Aim::Box(spelled("nk")),
                law: Law::NotNot,
                dir: Direction::Backward,
                pick: Pick::First,
                readers: Some(Readers::For(vec![
                    Reader::Box(spelled("qm")),
                    Reader::Output(0)
                ])),
            }
        );

        let entries =
            parse_hant("proof p = lhs(on(#nk in0, tuple-cancel, except(#qm))) diagram;").unwrap();
        let [Step::Rewrite { tactic, .. }, _] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        let Tactic::State { readers, .. } = tactic.as_ref() else {
            panic!("{:?}", tactic)
        };
        assert_eq!(
            *readers,
            Some(Readers::Except(vec![Reader::Box(spelled("qm"))]))
        );

        // And every way of writing one wrong, answered where it is written.
        for (proof, expected) in [
            (
                "proof p = lhs(at(#nk, not-not, for())) diagram;",
                "names no readers",
            ),
            ("proof p = lhs(at(#nk, not-not, for)) diagram;", "expects"),
            (
                "proof p = lhs(at(#nk, not-not, for(#q), except(#q))) diagram;",
                "takes one",
            ),
            (
                "proof p = lhs(on(#nk in0, tuple-cancel, for(#i7))) diagram;",
                "is not one of the letters",
            ),
        ] {
            let err = parse_hant(proof).unwrap_err();
            assert!(err.contains(expected), "{}: {}", proof, err);
        }
    }

    /// The law table is [`Law::name`]'s, read backwards, so the surface
    /// spells every law the table has and spells each of them once.
    #[test]
    fn every_law_the_table_has_can_be_named() {
        for law in Law::every() {
            assert_eq!(parse_laws(law.name()).unwrap(), vec![law], "{}", law);
        }
        // The one list left with a name of its own.
        let group = "branching";
        assert!(parse_laws(group).unwrap().len() > 1, "{}", group);
        assert!(one_law(group).is_err(), "{}", group);
    }

    /// A list's last comma is optional, so the same proof is written with
    /// it and without it, and the two parse to the same strategy.
    #[test]
    fn a_list_may_end_on_its_separator() {
        for (spelled, bare) in [
            (
                "proof p = lhs(saturate(fold, not-not,)) diagram;",
                "proof p = lhs(saturate(fold, not-not)) diagram;",
            ),
            (
                "proof p = lhs(fire(fold,)) diagram;",
                "proof p = lhs(fire(fold)) diagram;",
            ),
            (
                "proof p = lhs(at(#nkz, not-not, backward,)) diagram;",
                "proof p = lhs(at(#nkz, not-not, backward)) diagram;",
            ),
            (
                "proof p = lhs(at(#nkz, fold, except(out0),)) diagram;",
                "proof p = lhs(at(#nkz, fold, except(out0))) diagram;",
            ),
            (
                "proof p = lhs(on(in1 in0, tuple-cancel,)) diagram;",
                "proof p = lhs(on(in1 in0, tuple-cancel)) diagram;",
            ),
            // The sides of a split have always allowed it; they are here
            // so that the one rule is stated over every list that has one.
            (
                "proof p = via { id(0) } (left: diagram, right: diagram,);",
                "proof p = via { id(0) } (left: diagram, right: diagram);",
            ),
            (
                "proof p = cases(#nk) (true: lhs(decide), false: lhs(decide),);",
                "proof p = cases(#nk) (true: lhs(decide), false: lhs(decide));",
            ),
        ] {
            let spelled = parse_hant(spelled).unwrap_or_else(|e| panic!("{}: {}", spelled, e));
            let bare = parse_hant(bare).unwrap_or_else(|e| panic!("{}: {}", bare, e));
            assert_eq!(
                format!("{:?}", spelled),
                format!("{:?}", bare),
                "a spared comma changed the proof"
            );
        }
    }

    /// A run of no steps is a step that does nothing, written — a tactic
    /// block, a whole strategy, and an arm alike — so that commenting a
    /// proof's steps out leaves a proof.
    #[test]
    fn a_run_of_no_steps_is_written() {
        let entries = parse_hant("proof p = lhs() rhs() both() diagram;").unwrap();
        let [
            Step::Rewrite {
                side: l,
                tactic: lt,
            },
            Step::Rewrite {
                side: r,
                tactic: rt,
            },
            Step::Rewrite {
                side: b,
                tactic: bt,
            },
            Step::Diagram,
        ] = &entries[0].strategy[..]
        else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!((*l, *r, *b), (OnSide::Lhs, OnSide::Rhs, OnSide::Both));
        for tactic in [lt, rt, bt] {
            assert_eq!(tactic.as_ref(), &Tactic::Seq(Vec::new()));
        }

        // The bodies that hold a sequence hold an empty one.
        let entries = parse_hant("proof p = lhs(repeat() try()) diagram;").unwrap();
        let [Step::Rewrite { tactic, .. }, Step::Diagram] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(
            tactic.as_ref(),
            &Tactic::Seq(vec![
                Tactic::Repeat(Box::new(Tactic::Seq(Vec::new())), None),
                Tactic::Try(Box::new(Tactic::Seq(Vec::new()))),
            ])
        );

        // A whole strategy, and an arm — which is a run of none rather
        // than an arm left out, the one an omitted side would have got.
        assert_eq!(parse_hant("proof p = ;").unwrap()[0].strategy, vec![]);
        let entries = parse_hant("proof p = via { id(0) } (left: , right: diagram);").unwrap();
        let [Step::Via { left, right, .. }] = &entries[0].strategy[..] else {
            panic!("{:?}", entries[0].strategy);
        };
        assert_eq!(left.as_deref(), Some(&[][..]));
        assert_eq!(right.as_deref(), Some(&[Step::Diagram][..]));
    }

    /// A run of none is a run; a missing argument is missing. `fire()`
    /// names no law, `inline()` no sentence, `for()` no reader — and each
    /// says so rather than standing for a step that does nothing.
    #[test]
    fn an_absent_argument_is_not_a_run_of_none() {
        for (proof, expected) in [
            ("proof p = lhs(fire()) diagram;", "a law list names no law"),
            (
                "proof p = lhs(saturate()) diagram;",
                "a law list names no law",
            ),
            ("proof p = inline() diagram;", "names no sentence"),
            ("proof p = lhs(at()) diagram;", "`at` names nothing"),
            ("proof p = lhs(on()) diagram;", "`on` names no wires"),
            (
                "proof p = lhs(at(#nkz, fold, for())) diagram;",
                "`for` names no readers",
            ),
        ] {
            let err = parse_hant(proof).unwrap_err();
            assert!(err.contains(expected), "{}: {}", proof, err);
        }
    }

    /// One separator is spared, and only the last: a list of nothing is
    /// still nothing, and a gap between two commas still names nothing.
    #[test]
    fn a_spared_comma_is_the_last_one_only() {
        for (proof, expected) in [
            ("proof p = lhs(fire(,)) diagram;", "names no law"),
            ("proof p = lhs(saturate(fold,,)) diagram;", "names no law"),
            ("proof p = lhs(at(#nkz,)) diagram;", "`at` names no law"),
            (
                "proof p = lhs(at(#nkz, fold,, backward)) diagram;",
                "a direction is `forward` or `backward`",
            ),
            ("proof p = lhs(on(in0,)) diagram;", "`on` names no law"),
        ] {
            let err = parse_hant(proof).unwrap_err();
            assert!(err.contains(expected), "{}: {}", proof, err);
        }
    }
}
