# Restructure the tactics language into two layers: rewrite scripts + script generators

## Context

The current tactics language (in `bytecode/src/bin/rewrite/`) is in an uncomfortable middle ground: 26 hand-written window-matching rules (`rules.rs`, 3.5k lines) that both *find* where to rewrite and *perform* the rewrite, driven by a combinator engine (`tactic.rs`). Inverse pairs are written twice, termination guards are baked into rule matchers, and there is no way to name a location or a direction.

The restructure splits this into two layers:

- **Lower layer — rewrite scripts.** A small set of powerful equations (`Rule2`). Each closes over arguments (numbers, values, nodes, program sequences) and generates an **LHS** and **RHS** — two program sequences asserted to behave identically. A **rewrite script** is a sequence of steps: (rule + args, precise location, direction Forward/Reverse). A mechanical **applier** consumes a script + a sentence tree and performs the transformations, failing loudly on any mismatch. New Rule2s are added sparingly.
- **Upper layer — tactics.** The tactic combinators and per-rule matchers become *generators* of rewrite scripts. The applier is the **sole mutator** of the tree; the engine only proposes steps.

Per the user: not much depends on the existing specifics — keep the overall vibe (window-local equations, the depth-gutter listing, fuel, `--check`, CLI shape, prose-heavy docs) but burn the specifics down and rebuild on a minimal equational core. Do **not** port all 26 rules; measures and termination guards move entirely to the generator layer (a script is finite by construction).

## Architecture

### Global precondition: non-recursive, total sentences

The whole apparatus is restricted to roots that are non-recursive **and total**. `main.rs` already refuses a `#[recursive]` root; it additionally refuses any root that can fail, via `bytecode::arity::failure_reachability` (public precisely for this consumer — see its doc comment). Both properties are closed over reachability (`check_arities` propagates `#[recursive]` up the call graph; `failure_reachability` is a fixpoint over it), so every node the tree can ever contain — including anything an `Unfold` splices in — is non-recursive and cannot reach `panic`/`assert`/`assert_eq`.

Consequences, which the equations should exploit:

- **`total_effect_free` collapses to "has a known arity."** The old `speculable` predicate existed to keep an `assert` hidden in a dip or call body from being run on a path that wouldn't have run it; no such node exists here. `annihilate` (and tranche 2's `speculate_branch`) may accept *any* node with a known arity — ops, dips, calls, branches alike — instead of a syntactic whitelist.
- **Arity is always known.** Unknown arity came from `#[recursive]` callees; with recursion excluded, every node has an inferable arity, so `--check`'s "learning an arity" case (`None → Some`) disappears, `net` comparison becomes strict equality of known values, and `ArityUnknown` becomes an internal error rather than an expected side condition. (Verify during stage 1; if a residual `None` case survives, keep the old tolerant comparison and say why.)
- **`Unfold`'s non-recursive side condition never bites** — the precondition guarantees it. Keep the cheap per-step annotation lookup anyway (a step should be safe on its own terms, and scripts are meant to be checkable in isolation), but the equation prose need not hedge.
- **Tranche-2 bool/branch laws lose their panic caveats** — e.g. `bool_identity`'s absorbing cases were `B; drop; push c` rather than `push c` only because `B` might fail; under the precondition the drop-form composes with `annihilate` to reach the simple form anyway.

Lifting the restriction later (recursive or partial roots) means reintroducing exactly these caveats, so each is marked at its use site with a comment naming this precondition.

### Location addressing (new — nothing like it exists today)

```rust
// location.rs
pub struct Location { pub descent: Vec<(usize, Selector)>, pub at: usize }
```

From the root sequence, each `(index, selector)` descends into a child body (`ir::Selector::{Then,Else,Body}` already exists); `at` is the window start in the final sequence. Display like `[3.then, 0.body] @5`.

**Path contract:** each step's `Location` addresses the tree *as produced by all preceding steps*. The engine gets this for free: it applies each step the moment it emits it, and while it is descended into a child body every ancestor frame is suspended mid-iteration, so ancestor indices cannot go stale.

### Rule2, Step, Script (`rule2.rs`)

```rust
pub enum Direction { Forward, Reverse }
pub enum Rule2 {
    Collapse { k: usize, j: usize, a: Vec<Node> },
    ElimDip0 { a: Vec<Node> },
    Interchange { x: Node, framed: Node, n: i64, m: i64 },  // framed carries LHS-side depth k; (n,m) is x's claimed arity
    Fuse { k: usize, a: Vec<Node>, b: Vec<Node> },
    Hoist { k: usize, x: Vec<Node>, then_arm: Vec<Node>, else_arm: Vec<Node>,
            then_origin: String, else_origin: String },
    Distribute { then_arm: Vec<Node>, else_arm: Vec<Node>, suffix: Vec<Node>, /* origins */ },
    FoldBranch { c: Value, then_arm: Vec<Node>, else_arm: Vec<Node>, /* origins */ },
    Eval { op: Instruction, inputs: Vec<Value> },
    Annihilate { x: Node, n: usize, m: usize },             // claimed arity of x
    Counit { d: usize },
    CopyConst { c: Value },
    CopyAssoc { d: usize },
    CancelTuple { n: usize },
}
impl Rule2 {
    fn name(&self) -> &'static str;
    /// Verifies every fact the args claim against the library, plus the
    /// equation's own side conditions. The applier MUST call this before
    /// generating either side; lhs/rhs assume it has passed.
    fn check(&self, prog: &Program) -> Result<(), SideCondition>;
    fn lhs(&self) -> Vec<Node>;   // pure functions of the args —
    fn rhs(&self) -> Vec<Node>;   // Program appears only in check()
}
pub enum StepKind {
    /// Invoke a law of the calculus.
    Rule(Rule2),
    /// Unfold a library definition (delta-reduction). Forward = old `inline`:
    /// `Call{depth, target}` becomes `expand_call(prog, depth, target)`.
    /// Reverse = *fold*: recognize the body in the window and replace it with
    /// the call — a direction the old system never had.
    Unfold { depth: usize, target: SentenceIndex },
}
pub struct Step { pub kind: StepKind, pub dir: Direction, pub loc: Location }
pub type Script = Vec<Step>;
```

**Rules are laws; unfolding is definitional.** Every Rule2 is a schematic equation valid for *any* instantiation of its args; `Call{k, S} = body(S)` is not — its validity is the axiom the library contributes by defining `S`. So it is a separate step kind, not a Rule2: the applier fetches the body from the library itself (`expand_call`), so no copy of library content ever rides in a script and there is nothing to claim. Its only side condition is that `target` is not `#[recursive]`.

**Rule args are self-contained; the applier re-checks every claim.** A Rule2 closes over everything its two sides are built from. Facts that originate in the library — the claimed arity of X in `Interchange`/`Annihilate` — are carried in the args, which makes `lhs()`/`rhs()` pure functions of the args. The applier is *required* to call `check(prog)` first, which verifies each claim against the authoritative source (claimed arities must equal `node_arity(prog, x)`) alongside the equation's own side conditions. A script is never trusted: it can only communicate a construction, and every fact it rests on is re-derived by the applier.

### The equation core (tranche 1) — 13 equations + definitional unfold, replacing 26 rules

| equation | LHS = RHS | side conditions / notes |
|---|---|---|
| `unfold(k, target)` *(StepKind::Unfold, not a Rule2)* | `Call{k,target}` = `expand_call(prog, k, target)` | target not `#[recursive]`; body read from the library by the applier, never carried in the script. Fwd = old `inline`; Rev = fold a body back into a call |
| `collapse(k, j, A)` | `dip k { dip j { A } }` = `dip (k+j) { A }` | old `expand` = Reverse at split `(1, k-1)` |
| `elim_dip0(A)` | `dip 0 { A }` = `A` (spliced) | old `flatten_call`; Reverse introduces a frame; generators must decline the empty-body identity firing |
| `interchange(X, D)` | `X ; D_k` = `D_(k-m+n) ; X`, `arity(X)=(n,m)` | `k ≥ m` (⟺ `j ≥ n` read from the RHS — one condition, two readings, so one equation covers old `sink` (Fwd) and `float` (Rev)). D is a `Dip` at **any** depth incl. 0, or a `Call` with **depth ≥ 1 only** (`Call{0}` is frameless — preserve `frame_depth`'s asymmetry, rules.rs:241). `check` verifies the claimed `(n,m)` equals `node_arity(prog, x)`; shifted-depth usize conversion must succeed |
| `fuse(k, A, B)` | `dip k { A } ; dip k { B }` = `dip k { A ++ B }` | |
| `hoist(k, X, A, B)` | `dip (k+1) { X } ; branch { A } { B }` = `branch { dip k { X } ; A } { dip k { X } ; B }` | old `unfactor_branch` = Fwd. Old `factor_branch` = a **3-step macro**: per-arm `elim_dip0` Reverse (wrap the shared prefix), then `hoist` Reverse at k=0. Arms match via `same_effect` (provenance-blind) |
| `distribute(A, B, C)` | `branch { A } { B } ; C` = `branch { A;C } { B;C }` | C a *sequence* (generalizes the old single-node rule). Fwd/Rev are genuine inverses — never in one fixpoint |
| `fold_branch(c, A, B)` | `push c ; branch { A } { B }` = `A` if **`c.truthy()`** else `B` | decide by `Value::truthy`, NOT `c == Bool(true)` as a type test — `push 1; branch` folds to the else arm |
| `eval(op, inputs)` | `push v1 … push vn ; op` = pushes of outputs | via shared `eval_op(inst, &[Value]) -> Option<Vec<Value>>` delegating to `bytecode::value::{truthy, numeric_cmp}`. Must reproduce the exact fold tables: comparisons push a flag too (`Less` on symbols → `push false; push false`), `tuple_length` on a non-tuple hands the value back + `false`. Subsumes `fold_const` + `fold_const_unary`; arithmetic ops become a trivial extension |
| `annihilate(X, n, m)` | `X ; drop^m` = `drop^n` | `check` verifies `(n,m)` equals `node_arity(prog, x)` — under the global precondition (total root) that is the *whole* condition; no `speculable`-style syntactic whitelist. Subsumes `annihilate_drop` (m=1) and `annihilate_flagged` (m=2), and covers calls/branches the old rules had to decline |
| `counit(d)` | `pick d ; drop` = ε | the old `Pick` special case in `annihilation()` — deliberately NOT an `annihilate` instance |
| `copy_const(c)` | `push c ; pick 0` = `push c ; push c` | |
| `copy_assoc(d)` | `pick d ; pick 0` = `pick d ; dip 1 { pick d }` | |
| `cancel_tuple(n)` | `tuple n ; untuple n` = **`push true`** (not ε) | |

**Tranche 2** (later, same framework): `retain_condition`, `bool_identity` (the 3-wide `yields_bool` neighbor condition), `specialize_equal` (its "settled" guard is purely a generator concern — good validation of the layering), `dup_natural`, `rebuild_copy`, `speculate_branch`, `pick_drop_to_roll`, `roll 0 = ε`.

### Applier (`applier.rs`)

```rust
pub fn apply_step(prog, tree: &mut Vec<Node>, step: &Step, idx: usize, check: bool)
    -> Result<SpliceInfo, ApplyError>;   // SpliceInfo { removed, inserted } for resume math
pub fn apply_script(prog, tree: &mut Vec<Node>, script: &[Step], check: bool)
    -> Result<(), ApplyError>;
```

Navigate `descent` with bounds/kind checks → `check()` side conditions → generate source side (`lhs` for Forward, `rhs` for Reverse; for `Unfold` the two sides are `[Call{depth, target}]` and `expand_call(prog, depth, target)`, built by the applier from the library) → compare window with `same_effect_seq` (make it `pub(crate)` in ir.rs; origins are provenance and must not count) → splice the other side. `--check` (net stack-effect via `seq_arity`, currently tactic.rs:577-597) moves here verbatim.

Error taxonomy — every variant carries step index, rule name, direction, rendered Location; sketches via `ir::sketch`:

```rust
pub enum ApplyError {
    PathIndex { depth, index, len },
    PathKind { depth, selector, found },        // e.g. Then into a Dip
    WindowRange { at, need, len },
    WindowMismatch { expected: String, found: String },
    SideCondition(SideCondition),               // RecursiveTarget, FrameTooShallow{k,m},
                                                // ClaimedArityMismatch{claimed, actual},
                                                // ArityUnknown (internal error under the
                                                // global precondition), UnsupportedOp, DepthOverflow
    NetChanged { before: Option<i64>, after: Option<i64> },
}
```

### Matchers (`matcher.rs`) — the upper layer's rule-finding

```rust
pub trait Matcher: Sync + Debug {
    fn name(&self) -> &'static str;
    fn width(&self) -> usize;
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>>;
}
pub struct PlannedStep { kind: StepKind, dir: Direction, rel: Location }  // window-RELATIVE location
pub const ALL_MATCHERS: &[&dyn Matcher]; // + matcher_by_name
```

Mostly mechanical transliteration of the old `Rule::rewrite` match arms: return args + direction instead of the replacement. One matcher name per *search direction* (`sink`/`float` are two matchers over one `Interchange` equation; `collapse`/`expand` likewise). `factor_branch` is the first multi-step macro (3 planned steps). Multi-step contract: all steps anchored at offsets ≥ 0 from the window start; step i+1's relative location addresses the window region as left by step i; the applier revalidates everything, so a wrong macro fails loudly instead of corrupting.

### Engine (`engine.rs`, replaces tactic.rs internals)

Keep the `Tactic` enum, `Outcome::{Changed,Unchanged,Failed}` algebra, `can_fail` rollback analysis, `Seq/Choice/Try/Repeat/RepeatN/Children/Into/Bu/Td`, and the `each`/`once` scan discipline (resume at `w.saturating_sub(width-1)`, driver-level only — never recorded in locations). Changes:

- `step()` now: `plan` → for each planned step { absolutize location (driver's threaded path + `w` + rel), `env.spend()`, `applier::apply_step`, push onto `env.script` }.
- Refactor `ir::child_bodies`/`selected_bodies` into one `child_seqs(node) -> Vec<(Selector, &mut Vec<Node>)>` so the driver can thread the path (`&mut Vec<(usize, Selector)>` push/pop while recursing — the `std::mem::take`/write-back pattern is compatible).
- `Env` gains `script: RefCell<Script>`, loses `stop_after`/`inert`/`log` (the stepper no longer needs replay instrumentation). Fuel: spend per emitted step (`factor_branch` now costs 3 — document with a test). Trace strings become `rule dir @ location`.
- **Rollback:** `Seq` is the only combinator that rolls back (the clone at tactic.rs:305). Where it takes `saved`, also take `mark = env.script_len()`; on `Failed`, truncate the script to `mark`. Fuel is not refunded.

**Governing invariant, restated three ways** (goes in the module doc + docs/tactics.md):
1. Matchers are position-blind: `plan` is a pure function of (window, library facts), locations window-relative.
2. Only the driver knows the absolute path, used solely to stamp `Location`s.
3. The applier depends only on (initial tree, script) and is the sole mutator — so **replaying the emitted script against a fresh build reproduces the final tree bit-for-bit** (`assert_eq!`). This is the headline test.

### What survives / what burns

- **Survives:** `ir.rs` (with the `child_seqs` refactor + `same_effect_seq` visibility), `program.rs`, `arity.rs`, `print.rs` (one signature adaptation — `print_sentence` takes `Env`+`Tactic`, print.rs:10 — easy to forget), `diff.rs`, `stack.rs`, `main.rs` shell. `script.rs`: tokenizer, `Span`/`ScriptError::render`, `Expr`/`Arg` parser, `Definitions` (shadowing/recursion rejection), the entire `COMBINATORS` table and nearly all its tests survive verbatim; only the rule registry rewires to matchers and the `PRELUDE` is rewritten smaller with new rule names (bool-family entries drop out until tranche 2).
- **Burns:** `rules.rs` (26 impls + ~1700 lines of window tests), `tactic.rs` internals, `debug.rs` replay machinery, most of `tests.rs` (rebuild a smaller derivation suite), `docs/tactics.md` rewritten in the same prose style.

### CLI

Keep `rewrite <dir> <sentence> -t <tactic>` flow. Add `--show-script`: one step per line — index, rule name, direction arrow, location, arg sketches. Defer a parseable text serialization + `--apply-script` (needs a node-sequence grammar; `Rule2` is deliberately a closed enum so serialization stays possible) — note as future work in docs.

### Stepper (`debug.rs` rebuild — gets strictly better)

Census = one engine run producing (final tree, script, ending). `goto n` = fresh `ir::build` + `apply_script(&script[..n])` — O(n) splices instead of the current quadratic replay-with-`stop_after`. `preview` renders step n's lhs/rhs sketches directly from the `Step`. `trace` reads the script. Command parser + its tests survive verbatim.

## Stages (each leaves `cargo test` green; run `./run_all_tests.sh` at each stage)

1. **Foundations (additive).** `location.rs`, `rule2.rs` (13 equations + `StepKind::Unfold`), `applier.rs`; `same_effect_seq` → `pub(crate)`. No `speculable`-style predicate is needed — the global precondition (non-recursive, total root) reduces totality conditions to arity lookups. Tests: per-equation lhs/rhs goldens (transliterated from rules.rs tests), side-condition rejections (including fabricated claims: a wrong arity on `Interchange`/`Annihilate` must be rejected by `check`; `Unfold` of a `#[recursive]` target must be rejected; a Reverse `Unfold` whose window is not the target's body must fail `WindowMismatch`), applier navigation + every `ApplyError` variant provoked, Forward∘Reverse = identity round-trips (incl. one exact-equality case pinning provenance), table-driven net-preservation (`net(lhs) == net(rhs)` over arg corpora). Old code untouched.
2. **Matchers (additive).** `matcher.rs`, tranche-1 set. Tests: `plan` + `apply_step` on a scratch tree equals the old rule's documented replacement (reuse expected values from rules.rs tests).
3. **Engine (parallel).** `engine.rs` + new `Env`. Port Outcome-algebra/rollback tests from tests.rs (~717-1707), add script-truncation-on-rollback assertions and the replay-invariant test. Old tactic.rs still drives main.rs; both compile side by side.
4. **Cutover (the one big commit).** Rewire script.rs to matchers; rewrite `PRELUDE`; switch main.rs to engine.rs; add `--show-script`; `--check` flows into the applier. Delete rules.rs + old tactic.rs. Prune tests.rs to derivations tranche 1 supports: factoring (tests.rs:357/372/385), annihilate family (411-480), dips/collapse/fuse (190-355), distribute+fold (1778-1876), inline/flatten (1878-2024), and the corpus sweep `rewrites_preserve_arity_across_the_corpus` (tests.rs:515) — now also asserting script replay across the corpus. The sharing-chain block (tests.rs:1040-1460) moves out with a tranche-2 marker.
5. **Stepper.** Rebuild debug.rs on script-prefix application as above.
6. **Docs.** Rewrite `docs/tactics.md`: the two layers, the equation table (args, LHS = RHS, side conditions), scripts + applier failure guarantees, the three-part invariant, combinators (section largely survives), stepping, future work (script serialization, tranche 2, smarter generators).

Commit per stage on branch `claude/tactics-language-restructure-rcyxnw`; push after the suite is green.

## Verification

- `cargo test` (workspace) + `./run_all_tests.sh` (adds the `.hana` integration suite) at every stage; fmt + clippy per CI (`.github/workflows/ci.yml`).
- Headline invariant: for every engine test and the corpus sweep, replay the emitted script against a fresh `ir::build` and `assert_eq!` the trees.
- End-to-end: `cargo run --bin rewrite -- tests <sentence> -t all --check --show-script` on a few sentences from `tests/main.hana`; `--step` walk of a factoring derivation; confirm out-of-fuel on `repeat(each(collapse); each(expand))` still prints a legible oscillation trace; confirm the tool refuses a recursive root and a fallible root with distinct, legible messages.
- Corpus sweeps iterate only roots passing both refusals (non-recursive AND total, via `failure_reachability`). Assert the surviving corpus is non-trivially large, so the totality restriction cannot silently empty the sweep and turn it vacuous.

## Risks

1. **Multi-step firings shift fixpoint dynamics** — `factor_branch` as a 3-step macro interacts with `each`'s rescan differently; prelude derivations may differ. Re-derive; don't chase firing-count parity.
2. **Script memory** — args clone subtrees (`Hoist` carries both arms). Acceptable now; `Rc<[Node]>` is a future lever.
3. **Provenance drift** — RHS origins are generator-chosen; listings may change cosmetically. Test against shape, not listings.
4. **Stage-4 commit is inherently large** — mitigated by pre-landing stages 1–3, not avoidable (both engines share the script.rs surface).
5. **`eval` divergence from the VM is a soundness bug** — keep `eval_op` delegating to `bytecode::value`; keep the corpus totality sweep (tests.rs:648) as backstop.
