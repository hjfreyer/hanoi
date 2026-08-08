# Equality saturation

`bin/prove` holds a claim to a proof, and `bin/replay` checks a proof with the
search taken away. Neither *finds* one. That is still a person with
`bin/rewrite`, iterating on a tactic until two listings agree.

This is a design for the missing half: put both sides of an identity into an
**e-graph**, apply the twenty-two equations until it saturates, ask whether the
two sides landed in the same class, and read the answer out as a `.hand`
derivation that `bin/replay` decides.

**The first half of it exists.** `prove --emit-egglog` writes the corpus out as
an egglog program — the equations as rewrite rules, the library as unfolding
axioms, each identity as two terms and a `check`:

```bash
cargo run --bin prove -- tests --emit-egglog identities.egg
egglog identities.egg
```

```text
posed 5 identities to identities.egg
```

All five claims the corpus states close, in one file, in about a tenth of a
second. What does *not* exist is the half that matters: nothing reads an answer
back. Until an explanation comes out as a `.hand` and replays, an e-graph
agreeing that two terms are equal is a rumour — see "Nothing here is trusted".

```bash
egglog identities.egg > explanation.json   # not yet: see the staging plan
hanoi-egglog explanation.json > out.hand
replay tests out.hand --complete           # the only part that has to be right
```

## The gap this fills

`docs/identities.md` already names it, in "What is not here yet":

> Today a proof is a blind search strategy: the tactic knows nothing about where
> it is meant to end up, and the author iterates with `rewrite` until the two
> listings agree.

and says which piece is worth having first:

> **Congruence is the piece worth having first.** If the current term is
> `P ; X ; S` and the goal is `P ; Y ; S`, the problem *is* `X = Y`: peel the
> shared prefix and suffix, pair up branch arms and dip bodies, and hand each
> sub-goal to an ordinary blind tactic.

An e-graph is congruence closure with a work list. Peeling a shared prefix is
not something it has to be taught: two terms that differ in one position are
already sharing every class they have in common, and the sub-goal *is* the pair
of classes that has not merged.

**An e-graph also has no sides.** A tactic rewrites the left and must arrive at
the right, which is why `prove` grew "meet in the middle up to inlining" — the
fold-back that runs the right-hand side's own unfold script backwards — and why
even that cannot reconcile a *frame*-shape mismatch, where a proof leaves frames
collapsed and sunk and a naturally-written right-hand side does not. Saturation
asserts both sides and asks one question afterwards. Directionality is a
property of the derivation that gets read out, not of the search.

Termination arrives handled, too. `docs/tactics.md` puts it on the generator: "a
script is finite by construction, so termination is entirely the generator's
problem", and `docs/identities.md` flags that a goal-directed driver would need
a measure it does not have. Saturation's answer is saturation — or a bounded
`(run N)` — rather than a measure per rule.

## Where it would sit

Two placements, and they are worth arguing rather than assuming.

**Outside, as a producer.** egglog runs as its own process. It reads a generated
`.egg` file and writes an explanation; a small translator turns that into
`.hand`; `bin/replay` decides. `docs/derivations.md` specifies this socket
already:

> A producer in another language needs to emit text and nothing else. It does
> not need to link this crate, parse `.hana`, or agree with anything about how a
> search should work […] What it does *not* have to get right is soundness — a
> wrong derivation is refused at the step that is wrong, with a line and a
> column.

**Inside, as a backend.** `prove --search egglog` beside the tactic engine, with
egglog as a library dependency of the `rewrite` crate. Convenient: no second
process, no serialization, a `Node` becomes an e-node directly. The costs are
real. `rewrite/Cargo.toml` today lists exactly one dependency, `bytecode`, and
`rewrite/src/lib.rs` says the calculus "never crosses a crate boundary and never
becomes an API" — a search engine linked next to it is a large thing sitting
inside a small deliberate wall. And it makes the wrong thing easy: once the
searcher is in-process, "the classes merged" is one refactor away from being
accepted as the answer, where the whole architecture rests on the applier being
the only thing that decides.

**Outside, then.** The trusted surface stays what `docs/derivations.md` says it
is — a parser and the applier — and it stays that size no matter how large the
search gets. `run_proofs.sh` already runs `prove --emit` into `replay`, so the
gate this has to pass through is built.

### The one real cost of outside, and how to retire it

An external encoder is a **second statement of the equations**, and a second
statement can drift from `rewrite/src/rule.rs`. A `birewrite` that says
`interchange` shifts the frame by `k - m + n` when the Rust says `k - n + m` is
a searcher that spends its time proposing steps the applier rejects.

So the `.egg` file is **generated, not written**. `prove --emit-egglog` walks
the same `Rule` enum that `Rule::lhs` and `Rule::rhs` walk, and emits the
patterns from it. Drift then requires editing the emitter without editing the
rule, which is a diff a reviewer sees. And the failure mode is a proof that does
not close, never a proof that closes wrongly.

## egg or egglog

Both are e-graph engines with proof support, and they are good at different
halves of this.

| | egg | egglog |
|---|---|---|
| directions | one `Rewrite` per direction | `birewrite` — one per equation, which is what `Direction` already is |
| side conditions | `Condition` closures, in Rust | datalog relations over facts the encoder dumps |
| arity | an `Analysis` with a `merge` | `(function … :merge …)`, lattice-valued, first-class |
| scheduling | a `RewriteScheduler` | `:ruleset` and `(run … :until …)` |
| proofs | `explain_equivalence` → a `FlatExplanation`: each term annotated with exactly one `forward_rule` or `backward_rule`, wrapped `(Rewrite=> name e)` or `(Rewrite<= name e)` | **not in 2.0.** Its changelog lists "proof preparation and term encoding", which is groundwork; no command hands back a chain of steps |

The egglog column is better for four of the five rows, and the reasons are not
incidental to this problem. Every Hanoi equation is stated once and read in both
directions, which is `birewrite` exactly. The side conditions are lookups into
tables the compiler already computes, which is datalog exactly. And arity is a
lattice, for a reason worth its own section below.

The egg column is better for the row that decides whether any of this works.
`(Rewrite=> name e)` is *a `.hand` step minus its named arguments*: an equation
by name, a direction, and a position in a term. The translator described below
is mostly a matter of reading that wrapper.

**So: encode for egglog, and treat the proofs row as the open risk.** That is
what the emitter does, and running it settled the other four rows in egglog's
favour — `birewrite`, the datalog side conditions, `:merge` on arity and
`:ruleset` scheduling all do exactly what the encoding wants. The proofs row did
not resolve: egglog 2.0 has the groundwork and not the feature, so the chain of
steps a derivation needs cannot yet be read out of it.

That does not invalidate the encoding, and it is worth being precise about why.
Everything below is a statement about *what the equations look like as rewrite
rules*, which is engine-independent; only the last step, reading an explanation,
is not. If it has to move to egg, arity goes from a `:merge` to an
`Analysis::merge` and the side conditions go from relations to `Condition`
closures. That is a port, not a rewrite.

## Encoding a term

A Hanoi term is a `Vec<Node>` — `rewrite/src/ir.rs`. Nodes first, because they
are the easy half.

```text
(datatype Node
  (Op    Instr)
  (Call  i64 Sentence)   ; depth, target
  (Dip   i64 Seq)        ; depth, body
  (Branch Seq Seq))      ; then, else
```

`Node::Dip` and `Node::Branch` carry provenance in Rust — `origins`,
`then_origin`, `else_origin` — and **none of it is encoded**. That is not a
simplification, it is the same decision made twice already. `same_effect`
deliberately is not the derived `PartialEq`, because "comparing those would make
provenance part of term identity", and `.hand` drops origins on the wire for the
same reason. An e-graph merges terms that are equal; if origins were encoded,
two identical blocks compiled from different places would sit in different
classes and congruence would find nothing. The encoding's notion of identity has
to be `same_effect`, and dropping provenance is what makes it so.

### Sequences are the whole problem

```text
(datatype Seq
  (Empty)
  (Cat Seq Seq))
(birewrite (Cat (Cat a b) c) (Cat a (Cat b c)))
(birewrite (Cat (Empty) a) a)
(birewrite (Cat a (Empty)) a)
```

A monoid, with associativity and unit as rules. This is the piece that decides
whether the design is practical, and it should be said plainly rather than
discovered in stage 4.

**Why not a cons list.** `(datatype Seq (Nil) (Cons Node Seq))` is cheaper and
has no associativity rules at all, and a fixed-width window anchored at the head
of any suffix matches fine — every suffix of every term is its own class. It
cannot bind a *middle segment*. Seven of the twenty-two laws do exactly that:

| law | the sequence variable |
|---|---|
| `annihilate` | `X ; drop^m` = `drop^n` — `X` is a whole sequence |
| `distribute` | `branch { A } { B } ; C` — `C` is a whole sequence |
| `hoist` | `X` under the frame, `A` and `B` the arms |
| `fuse` | `A` and `B`, the two bodies |
| `collapse` | `A`, the inner body |
| `elim_dip0` | `A`, the body being spliced |
| `copy_nat` | `X`, the computation being copied |

`annihilate` alone is the reason: `docs/tactics.md` notes it "subsumes the old
`annihilate_drop` (m=1), `annihilate_flagged` (m=2) and the case with no drops
at all", and read backward it is `introduce`, which is how a cancelling pair
gets into a term in the first place. A search that cannot use it backward cannot
find most of the interesting proofs.

**And associativity is where equality saturation blows up.** That much was
predicted, and it is true. What was *not* predicted is the other half, which the
first run settled:

> Associativity is both the blowup and unnecessary — for this corpus, so far.

With `(saturate (run assoc))` in the schedule, `discarded_work_on_copies` runs
past ninety seconds without closing. With it off, the same claim proves in about
twenty milliseconds, and so do the other four. The reason is that a term is
emitted **right-associated** and every law is written against that spine, so a
window whose sequence variable is a single node or a suffix is already matchable
— and that is most of them, `annihilate` included. Re-association earns its cost
only for a variable spanning several nodes away from a spine boundary, and
nothing in the corpus needs one yet.

So associativity is emitted, in its own ruleset, and left **out of the default
schedule** with a note saying when to reach for it. The unit laws are a separate
ruleset and are always on: they only ever shrink a term, and they are not
optional, because a law that leaves nothing behind leaves an `(Empty)` in the
spine that a one-node right-hand side has to meet. `testing_a_test_by_name` is
the claim that says so — it fails without them.

The fallback if a claim ever does need mid-sequence matching is unchanged:
bounded widths, which is what a matcher does today anyway — `docs/tactics.md`
observes that "a matcher's width is fixed before it looks".

### Instructions and values

`Instr` mirrors `bytecode::Instruction` and `Val` mirrors `bytecode::Value`, one
constructor each. Two rules carry over from the wire format in
`docs/derivations.md`, for the same reasons:

- a **`Sentence`** is its fully qualified name, never a `SentenceIndex`, because
  "an index is an offset into one assembly of one corpus";
- a **`Symbol`** is its declared path, because a `Symbol` compares by an `id`
  minted during assembly.

`panic`, `assert` and `assert_eq` have no constructor, matching the format's
refusal to spell them: every equation here is stated about code that cannot
fail, and the global precondition is checked before any of this runs.

## The equations

Twenty-two `birewrite`s, generated from `Rule`. Three worth showing.

**`counit` — `pick d ; drop` = nothing.** No conditions, no sequence variables:

```text
(birewrite (Cat (Op (Pick d)) (Cat (Op (Drop)) rest)) rest)
```

**`interchange` — `X ; D_k` = `D_(k-m+n) ; X`, for `X : n -> m`, `k >= m`.** The
one piece of real arithmetic, and the first rule that needs a fact:

```text
(rule ((= lhs (Cat x (Cat (Dip k body) rest)))
       (= (arity x) (Ar n m))
       (>= k m))
      ((union lhs (Cat (Dip (+ (- k m) n) body) (Cat x rest)))))
```

Written as a `rule` rather than a `birewrite` because the condition names `k`
and `m` from one side; the reverse reading is a second `rule` generated
alongside it, with `j >= n` — which `docs/tactics.md` notes is the same
condition read from the other end.

**`copy_nat` — `pick (n-1)^n ; X ; dip m { X }` = `X ; pick (m-1)^m`.** Both
hard things at once: a sequence variable and an arity. It is also the law that
needs `X` to be deterministic, which the encoding gets for free — an e-graph has
no notion of a term that answers differently on two occasions.

## Facts the searcher cannot re-derive

`rewrite/src/rule.rs` is explicit that "**a script is never trusted.** It
communicates a construction, and every fact that construction rests on is
re-derived by the applier." A searcher in another process cannot do that. It has
no `Library`. So the encoder dumps the facts as tables:

| table | source |
|---|---|
| `(function op-arity (Instr) Arity)` | `bytecode::arity::op_arity` |
| `(relation commutative (Instr))` | `Instruction::commutative` |
| `(relation yields-bool (Instr))` | `Instruction::yields_bool` |
| `(function evaluates (Instr ValList) Seq)` | the `eval` equation's answers |
| `(function body (Sentence) Seq)` | `Library::sentences`, for `unfold` |

**A wrong table costs a rejected derivation, never a wrong proof.** Every one of
these is re-derived by `Rule::check` when the step is applied, against the real
program — that is what `SideCondition::ClaimedArityMismatch` and
`NotCommutative` and `NotBoolResult` are for, and `docs/derivations.md` shows
one being caught with a line and a column. The tables are a *hint about where to
look*, which is the only kind of thing a searcher ever produces.

Two of them are measured rather than asserted, which is worth knowing:
`Instruction::commutative` and `Instruction::yields_bool` are swept against the
interpreter over every operand shape. Dumping them into egglog copies a checked
fact, not a comment.

## Arity is not a property of an e-class

This is the subtlest thing in the design, and getting it wrong produces a search
that runs happily and proposes steps the applier refuses.

`interchange`, `annihilate`, `copy_nat` and `unframe` all take an arity `n -> m`
as an argument. The obvious encoding is an e-class analysis: a function from
`Seq` to `Arity`, computed bottom-up, joined on merge. But **arity is not
invariant across an e-class.** `docs/identities.md` says so about identities:

> `pick 1 ; drop` = nothing is `(2 -> 2)` against `(0 -> 0)` — both leave the
> stack as they found it, but the left needs a value to look at where the right
> does not.

What *is* invariant is the net change `m - n`. The input requirement `n` is an
upper bound that falls when two terms are unioned. So the analysis is a genuine
lattice — `min` on `n`, with `m` carried as `n + net` — and `:merge` is exactly
the mechanism for it. This is the row where egglog earns its place.

**And the analysis is a firing filter, not the source of the argument.** The
resolution is the sentence the rest of the design hangs on:

> The e-graph decides which steps to try. The concrete term chain decides what
> gets written down.

An explanation is a chain of *concrete* terms — `t0, t1, … tk` — not a chain of
classes. When the translator emits `annihilate(x = { … }, n = 1, m = 1)`, the
`n` and `m` come from running the same arity computation `rewrite/src/arity.rs`
uses over the concrete `x` it found at that position in `t_i`. The lattice value
is only ever consulted to decide whether a rule was worth firing, where being
conservative costs a missed step and nothing else.

### The real limitation is a generative reading, not associativity

An egglog pattern may only build what its left side binds. That rules out every
backward reading which invents material the pattern cannot name — `counit`
backward has to produce a `d` from nothing, `annihilate` backward an entire `X`
— and those are not emitted at all. `annihilate` backward is `introduce`, which
is how a cancelling pair gets into a term, so this is a real loss rather than a
bookkeeping one.

But "generative" turns out to be two things, and only one of them is fatal:

| | example | emitted? |
|---|---|---|
| the pattern cannot bind what the result needs | `counit`, `annihilate`, `fuse`, `cancel_tuple` backward | no — egglog would refuse the rule |
| everything is bound, but it fires on its own output forever | `elim_dip0` backward, `commute` backward | yes, if it is **run** rather than **saturated** |

The second row is the useful discovery. `elim_dip0` backward puts a frame that
hides nothing around the head of a sequence, which is how factoring starts — a
shared prefix has to be *in* a frame before `hoist` can lift it out of two arms.
Saturating it nests frames forever. Running it once per round nests it exactly
as deep as there are rounds, which is enough: `a_value_tested_twice` is the
corpus claim that turns on this, and it does not close without it.

So the distinction worth carrying forward is not generative versus not. It is
**a reading that cannot be searched** versus **a reading that has to be
scheduled**.

## From an explanation to a derivation

The translator is four steps, and it is the only new code with any subtlety in
it.

1. **Read the chain.** An explanation is `t0 … tk`, each adjacent pair annotated
   with one rule name and one direction — `Rewrite=>` is `->`, `Rewrite<=` is
   `<-`, matching `Direction::Forward` and `Direction::Reverse`.
2. **Turn the position into a `Location`.** The rewrite wrapper sits at exactly
   one place in the term tree. Walk from the root: every `Dip` body descended
   through appends `(index, Selector::Body)`, every branch arm appends
   `(index, Selector::Then)` or `Else`, and the offset along the `Cat` spine at
   the final level is `at`. That is `Location { descent, at }` verbatim, and it
   prints as `[1.then, 2.body] @2`.
3. **Recover the named arguments.** Match the equation's left-hand side pattern
   against the subterm at that position; library-sourced arguments are
   recomputed from the concrete term, per the section above.
4. **Emit.** `equation(args) -> [descent] @at;`, with the argument names from
   `serial::arg_names` — `collapse` takes `k, j, a`, `interchange` takes
   `x, framed, n, m`, and so on. `docs/derivations.md` has the table.

Two things fall out that are worth stating rather than rediscovering.

**Locations are relative to the tree as prior steps left it**, which
`docs/derivations.md` warns producers about: "step 5 may name an index that did
not exist when step 4 was written." Here it is automatic, because `t_i` *is*
that tree. The translator never has to reason about it.

**Associativity and unit steps are dropped, not translated.**
`(Cat (Cat a b) c)` and `(Cat a (Cat b c))` are the same `Vec<Node>`. Those
rules are bookkeeping in the encoding, not equations of the calculus, and they
have no `.hand` spelling because there is nothing for them to say. So the
translator flattens each `t_i` to a `Vec<Node>` and skips any pair whose two
sides flatten identically. This is the one place where the encoding's rules and
the language's laws must be told apart, and the test for it is that the emitted
derivation's step count matches the number of non-bookkeeping pairs.

### A worked one

`tests/identities.hana` states:

```hana
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

Its derivation today, from `prove --emit`:

```text
proof identities::testing_a_test {
    bool_result(op = is_bool) -> @0;
    annihilate(x = { is_bool }, n = 1, m = 1) -> @0;
}
```

Through the pipeline: the encoder emits both sides as `Seq` terms and a
`(check (= lhs rhs))`; saturation merges them; the explanation is a three-term
chain whose two hops name `bool_result` forward and `annihilate` forward, each
wrapped at the root of the spine; the translator reads `@0` off both, recomputes
`is_bool`'s arity as `(1, 1)` from `op_arity`, and writes the same four lines.
`replay tests out.hand` then decides it, sharing no code with any of the above.

That the answer is *the same derivation the tactic finds* is the stage-2 gate,
not a claim — a different derivation of the same identity is equally acceptable,
and the check is `replay`, not a diff.

## `unfold` and the library

`unfold` is not an equation of the calculus. It is "the axiom the *library*
contributes by defining `S`", and a script names a sentence and never quotes it.
In the e-graph it is one rule over the `body` table:

```text
(rewrite (Call 0 s) (body s))
(rewrite (Dip k (body s)) (Call k s))   ; the same, read the other way
```

The second line is the interesting one. `docs/identities.md` calls folding a
body back into a call "the real gap", because "nothing can read a window and say
which sentence to fold into" — a limitation on searching, which is why the
fold-back today is generated by inverting the right-hand side's own unfold
script. Congruence does not have that limitation: the body is in a class, the
class contains the call, and the merge is already there. `inv(unfold)` becomes
an ordinary step the search can find.

The cost is the obvious one. Expansion is finite — the global precondition
refuses `#[recursive]` sentences, so there is no infinite unfolding — but finite
is not small, and `tests/string.hana` is 2,600 lines of it. So `body` is
populated only for sentences reachable from the two sides, to a depth, and
`unfold` lives in its own ruleset run on its own schedule. Stage 4, deliberately
after the sequence laws.

## What this reaches that a tactic cannot

**The three laws with no matcher.** `roll_cycle`, `unframe` and `pick_roll` are
equations a script may name, but `docs/tactics.md` records that "there is no
matcher for any of the three, so a tactic cannot ask for one", because what each
of the six readings should look for is an open question about search. A
`birewrite` needs a pattern and not a matcher, so all six readings arrive at
once, and the question stops needing an answer.

**Folding.** Above.

**Identities as rules.** `docs/identities.md` lists this first under "What is
not here yet": a proven identity should be citable in another proof. In an
e-graph it is one `birewrite` per identity, generated from the `Library`'s
`identities` table the same way the axioms are generated from `Rule`. The
acyclicity worry the same section raises — a proof of A citing B whose proof
cites A — becomes a question about which ruleset each identity is loaded into,
which is a scheduling decision rather than a topological sort.

What it does **not** reach is anything new about truth. Everything the search
finds is a consequence of the same twenty-two equations plus the library's
unfolding axiom, and every one of them is re-checked when the derivation is
replayed. `docs/identities.md` says this about a goal-directed engine and it is
just as true here: it "cannot make a wrong rewrite possible, only a right one
easier to find."

## Staging it

Each stage ends at something runnable.

0. ~~**The spike.**~~ **Done, and it changed the plan.** The encoding loads and
   all five corpus identities close — but egglog 2.0 ships proof *preparation*,
   not proof extraction, so the kill criterion this stage existed to test has
   not actually been met. That risk moves to stage 2, and it is now the whole
   risk.
1. ~~**The encoder.**~~ **Done.** `prove --emit-egglog <file>` — sorts, the fact
   tables, the equations, the reachable library as unfolding axioms, and one
   `(check (= lhs rhs))` per identity. `--filter` narrows it to one claim, which
   is the only comfortable way to read a failure, since `check` stops the run at
   the first one. It lives in `rewrite/src/egglog.rs`, and the shape of its
   output is held by `tests::every_identity_poses_to_an_egraph` — nothing in the
   build has an egglog to run, so that test is what keeps it from rotting.
2. **The translator.** Explanation → `.hand`. **Gate: `replay tests out.hand`
   accepts all five.** Blocked on extraction: if egglog will not give a chain of
   concrete terms with rule names and directions, this is where the port to egg
   happens, and the encoding carries over with arity moving from a `:merge` to
   an `Analysis::merge`.
3. **The equations still missing.** `eval` wants a literal that is not opaque;
   `copy_nat` and `unframe` are stated with repetition counts the way
   `annihilate` is, and want the same instantiation. `copy_nat` is the one worth
   reaching for, being the law that is genuinely independent.
4. **Sequence variables**, if a claim ever needs one. Associativity is already
   emitted and already off; turning it on is a schedule edit, and the numbers to
   beat are in the section above.
5. **Identities as rules**, and a `--complete` run over the whole corpus.

## What could go wrong

- ~~**Associativity blows the e-graph up.**~~ Measured: it does, and it is not
  needed. Off by default, with bounded-width firing still the retreat if a claim
  ever wants it.
- **The derivations are ugly.** Explanation length is not minimized in general.
  `proof copying_a_constant` is three steps written by hand; saturation may
  produce thirty that are all correct. `replay` will not care, and a person
  reading `--show-script` will. Shortest-explanation search exists and is not
  free.
- **Proof extraction is the newest part of egglog, and 2.0 does not have it.**
  Its changelog lists "proof preparation and term encoding", which is the
  groundwork rather than the feature. This is the only thing now standing
  between the emitter and a derivation, which is why stage 2 carries an explicit
  port-to-egg branch rather than a hope.
- **The encoder drifts from `rule.rs`.** Mitigated by generating it, and by the
  fact that drift shows up as proofs that stop closing.

## Nothing here is trusted

The generated `.egg`, the engine, the explanation, the translator: all of it
sits outside the line `docs/derivations.md` draws.

> **Nothing about being written down makes a step trusted.** Facts that
> originate in the library ride in the arguments […] and are re-derived against
> the real program on every application.

So the encoder can mis-state an equation, the analysis can compute a wrong
arity, the translator can emit a location that names nothing, and the search can
find a derivation of something false — and every one of those is a proof that
fails to replay, at the step that is wrong, with a line and a column. The
trusted surface is the same parser and the same applier it was before, and
adding a search engine to the outside of the system does not add a byte to it.

That is the whole argument for doing this as a producer.

## See also

- [docs/derivations.md](derivations.md) — the format this produces, and the
  producer contract it is written against.
- [docs/tactics.md](tactics.md) — the twenty-two equations this encodes, and the
  search this is an alternative to.
- [docs/identities.md](identities.md) — the claims a derivation discharges, and
  the "What is not here yet" list this is an answer to.
