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

All five claims the corpus states close, in one file, in about forty
milliseconds — each in its own `push`/`pop` scope, because identities are
independent claims and sharing an e-graph between them makes each one's cost
depend on its neighbours.

What does *not* exist is the half that matters: nothing reads an answer back.
Until an explanation comes out as a `.hand` and replays, an e-graph agreeing
that two terms are equal is a rumour — see "Nothing here is trusted".

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

### A sequence is a cons list, and that is the whole design

```text
(datatype*
  (Node (Op Instr) (Call i64 String) (Dip i64 Seq) (Branch Seq Seq))
  (Seq  (Empty) (Cons Node Seq)))

(constructor app (Seq Seq) Seq)
(rewrite (app (Empty) b) b            :ruleset splice)
(rewrite (app (Cons n a) b) (Cons n (app a b)) :ruleset splice)
```

The obvious encoding of a concatenative language is a **monoid** — `Cat`, with
associativity as a rewrite — and it is a trap. Every re-association of a term is
a distinct e-node, a window will not match until they all exist, and building
them all is where equality saturation goes to die. Measured, on this corpus:
with associativity saturating, `discarded_work_on_copies` runs past ninety
seconds without closing; without it, twenty milliseconds.

A **cons list** gives a sequence exactly one spelling, so a window matches where
it sits, with nothing normalized first. There is no associativity ruleset at all
— not one that is off by default, one that does not exist.

What a cons list costs is concatenation, which five laws need on their
right-hand sides: `elim_dip0`, `fuse`, `distribute`, `fold_branch`, `retest`.
That is bought back with `app` and two reduction rules, and the reason it is not
associativity wearing a hat is the property to hold onto:

> **No pattern contains an `app`.** It is built and reduced away, never searched
> for.

Reduction walks one cons cell at a time and terminates. Search does not.

#### A whole subsequence is a node

Seven laws quantify over a subsequence. Four of them — `collapse`, `hoist`,
`fuse`, `distribute` — want a Dip body or a branch arm, which is a *field* of a
node rather than a span of the spine, and a cons list binds those without
trouble.

The other three — `annihilate`, `interchange`, `copy_nat` — want a run of nodes
sitting in the sequence. They take a single `Node` instead, and the packaging is
done by the calculus:

| step | what it does |
|---|---|
| `elim_dip0` backward, twice | each of two nodes becomes `dip 0 { · }` |
| `fuse` at `k = 0` | the two frames become one, holding both |
| `annihilate` | fires, with the frame as its single `X` |
| `elim_dip0` forward | the survivor is spliced back |

Every one of those is an instance of a law. That is the same trade
`docs/tactics.md` already makes for factoring — "three steps, each of which is
an instance of a law, instead of one rule that knew a whole procedure" — and it
is why the encoding needs no rule that spans the spine.

`Node::Call` is this idea already in the language: a whole sentence body, worn
as one node. Which is why unfolding is stated at the node level and needs no
splicing at all — see "`unfold` and the library".

#### What it gives up

`distribute` backward, which factors a shared *suffix* out of two branch arms.
Finding one means splitting a cons list at a point nothing names, and that is
exactly the search a monoid would have paid for. `docs/tactics.md` notes this
reading is one "the old set could not do at all", so nothing regresses — but it
is the one thing on the other side of the ledger, and it is worth knowing which
way the trade went.
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

**`counit` — `pick d ; drop` = nothing.** No conditions, no sequence variables.
Forward only: read backward it has to invent a `d`, and then another.

```text
(rewrite (Cons (Op (Pick d)) (Cons (Op (Drop)) rest)) rest :ruleset laws)
```

**`interchange` — `X ; D_k` = `D_(k-m+n) ; X`, for `X : n -> m`, `k >= m`.** The
one piece of real arithmetic, and the first rule that needs a fact:

```text
(rule ((= s (Cons x (Cons (Dip k b) rest)))
       (= i (ar-in x)) (= v (ar-net x)) (>= k (+ i v)))
      ((union s (Cons (Dip (- k v) b) (Cons x rest))))
      :ruleset laws)
```

Written as a `rule` rather than a `birewrite` because the condition names `k`
and the arity from one side; the reverse reading is a second `rule` generated
alongside it, with `j >= n` — which `docs/tactics.md` notes is the same
condition read from the other end. And `x` is one `Node`, per the section above,
so a `dip 0` frame carries a multi-node `X` through the same rule.

**`fuse` — `dip k { A } ; dip k { B }` = `dip k { A B }`.** The concatenation
case, and the one that has to be built rather than matched:

```text
(rewrite (Cons (Dip k a) (Cons (Dip k b) rest))
         (Cons (Dip k (app a b)) rest)
         :ruleset laws)
```

Forward only — read backward the split point is free. At `k = 0` this is also
the step that turns two framed nodes into one framed pair, which is how a
multi-node window gets packaged.

**`copy_nat` — `pick (n-1)^n ; X ; dip m { X }` = `X ; pick (m-1)^m`.** Not
emitted yet: the repetition counts want the same instantiation `annihilate`
gets. Worth noting anyway that the one condition it carries for free is the
hard one — it needs `X` deterministic, and an e-graph has no notion of a term
that answers differently on two occasions.

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
`a_value_tested_twice` is the corpus claim that turns on it, and does not close
without it.

Bounding it by schedule alone is not enough. Framing every head, once per round,
puts a fresh `dip 0` on every cons cell, `elim_dip0` unwraps each one back
through `app`, and `discarded_work_on_copies` stops finishing. What works is
**aiming** it: fire only where both branch arms already begin with the same
node, which is exactly the precondition of the step that consumes the result.
Cost then is nothing measurable.

That is not a new axiom — it is two instances of `elim_dip0` at named positions,
which is precisely what a matcher is. So the distinction worth carrying forward
is not generative versus not. It is **a reading that cannot be searched**, a
reading that has to be **scheduled**, and a reading that has to be **aimed** —
and the third is the one that looks like the tactic layer, because it is.

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

**`splice` steps are dropped, not translated.** `(app a b)` and the cons list it
reduces to are the same `Vec<Node>`. Those two rules are bookkeeping in the
encoding, not equations of the calculus, and they have no `.hand` spelling
because there is nothing for them to say. So the translator flattens each `t_i`
to a `Vec<Node>` and skips any pair whose two sides flatten identically. This is
the one place where the encoding's rules and the language's laws must be told
apart, and the test for it is that the emitted derivation's step count matches
the number of non-bookkeeping pairs.

The cons encoding earns something here that a monoid would not have: there is
one bookkeeping rule set instead of two, and it only ever *shrinks*, so the
skipping is a local check rather than a normalization pass.

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
In the e-graph it is one `birewrite` per sentence, stated at the **node** level:

```text
(let $b_drop_and_true
  (Cons (Op (Drop)) (Cons (Op (Push (Lit "true"))) (Empty))))
(birewrite (Call k "identities::drop_and_true") (Dip k $b_drop_and_true)
           :ruleset unfold)
```

`k` is free on both sides, so one rule covers every depth, and **nothing is
spliced**. That is not a trick to dodge concatenation: `ir::frame_depth` already
treats a `Call` and a `Dip` as the same thing differing only in whether the body
is written out. Getting from `(Dip 0 body)` into the enclosing sequence is then
`elim_dip0` — an equation, with a name, that shows up in the derivation —
rather than something the unfolding rule does on the side.

Read backward it folds, and that is the interesting direction.
`docs/identities.md` calls folding a body back into a call "the real gap",
because "nothing can read a window and say which sentence to fold into" — a
limitation on searching, which is why the fold-back today is generated by
inverting the right-hand side's own unfold script. Congruence does not have that
limitation: the body is in a class, the class contains the call, and the merge
is already there. `inv(unfold)` becomes an ordinary step the search can find.

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

- ~~**Associativity blows the e-graph up.**~~ Measured: it does. It is also not
  needed — the encoding is a cons list and has no associativity ruleset at all.
  What replaced it is `app`, which is only ever built and never matched.
- **A claim proved to be `nothing` poisons the empty sequence.**
  `discarded_work_on_copies` puts a four-node program into `(Empty)`'s class,
  and `(Empty)` is the tail of every term in the file — so every suffix position
  in every other claim starts matching a program. That is why each identity gets
  its own `push`/`pop` scope, and it is a hazard for any future encoding that
  shares one graph across claims.
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
