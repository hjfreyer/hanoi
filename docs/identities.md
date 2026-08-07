# Identities

`bin/rewrite` can show that two programs are interchangeable. Until an identity
existed that was all it could do: the showing was printed and lost, nothing
re-checked it when the library changed underneath, and nothing could cite it
later.

An **identity** is the claim, written in the `.hana`. Its **proof** is a tactic,
written in the `.hant` beside it. `bin/prove` holds the two together.

```bash
cargo run --bin prove -- tests
```

```
Proving 4 identities...
identity identities::testing_a_test ... ok (2 steps)
identity identities::a_value_tested_twice ... ok (6 steps)
identity identities::copying_a_constant ... ok (3 steps)
identity identities::discarded_work_on_copies ... ok (3 steps)

identity result: ok. 4 passed; 0 failed; 0 filtered out
```

## Stating one

```hana
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

Two inline bodies, and **only** two inline bodies. Naming two sentences that
already exist is `{ jump a } = { jump b }`, so one form covers both cases; a
second spelling would buy nothing and cost the consistency between them. A body
is whatever a sentence body is, so `branch { } { }` and `dip 1 { ... }` work
inside one for free.

`#[arity(n, m)]` and `#[total]` are the annotations an identity may carry, each
a claim both sides answer for independently. The rest name properties of a
sentence *being called*, which an identity is not, so they are refused rather
than ignored — an annotation nothing reads is a lie. `export` and `test` are
refused for the same reason: nothing calls an identity and nothing runs it.

### It is core, not sugar

`docs/compilation.md` asks: could a user have written this by hand in terms of
other surface constructs? A `sentence` names code and a `test sentence` runs it,
and neither states an equation. So `identity` lowers to itself, and the
sugar/core seam grows by one variant on each side rather than by a lowering.

### The two sides are sentences

Each side is compiled into the library as an ordinary sentence, named
`<identity>::lhs` and `<identity>::rhs`. Nothing resolves to those names —
`jump foo::lhs` is refused, because an identity is declared into the module
namespace as an identity, not as a sentence — but `Library::names` is what
`resolve_sentence` reads, so **`rewrite` can address a side directly**:

```bash
$ rewrite tests 'copying_a_constant::lhs' -t 'once(inv(share { push 9 }))' --show-script
$ rewrite tests 'copying_a_constant::rhs'
```

That is the loop a proof gets written in: explore with `rewrite` until the two
listings agree, then move the tactic into the `.hant`.

It is also the decision the next feature rests on. When a derivation may cite an
identity, the applier will regenerate both sides from the library on every
application — exactly as it already regenerates an unfolded body — so no copy of
a program ever travels inside a script, and a script written against a library
that has since changed fails at the step that stopped fitting rather than
rewriting by a stale claim.

### What the compiler checks

One thing, and it is the one property of an identity that is about the
*statement* rather than about a proof: **the two sides must leave the stack the
same**.

Net change, not full arity. `pick 1 ; drop` = nothing is `(2 -> 2)` against
`(0 -> 0)` — both leave the stack as they found it, but the left needs a value
to look at where the right does not. Every counit reads this way, and so does
every annihilation, which lowers the input requirement on purpose. `--check` in
the rewriter allows the same asymmetry for the same reason; refusing it here
would refuse exactly the equations the rewriter is built out of.

Deliberately *not* checked by the compiler: non-recursive, and unable to fail.
Those are the preconditions the rewriter's equations are stated under —
conditions on provability rather than on well-formedness — and asking for them
in `assemble_source` would tie the language to a particular rule set. `prove`
asks, in the words `rewrite` uses.

## Proving one

```
// tests/identities.hant
proof testing_a_test = cleanup;

proof copying_a_constant =
    must(once(inv(share { push 9 })));
    must(at(0, sink));
    must(at(0, flatten));
```

A `.hant` is the tactic language of `docs/tactics.md` with one definition form
added:

```text
def := "tactic" ident "=" expr ";"
     | "proof"  path  "=" expr ";"
```

so a file may define its own tactics and then prove with them.

### Why the proof is not in the `.hana`

A proof is not part of the program. It depends on the rewriter's rule set,
which is not part of the language, and it changes when that rule set does while
the claim it establishes does not. Keeping it out means an identity reads as a
statement rather than as a script.

### One-sided

The tactic rewrites the **left-hand side**; the result must be the right-hand
side. Every step is an equation, so what a run leaves behind is a derivation
LHS ⇒ RHS: one linear script, which is a thing that can be replayed, printed,
stepped through and diffed.

**The cost is that the right-hand side has to be written in the form the tactic
lands on.** `{ jump foo }` on the right only works when the proof leaves the
left as an unopened call to `foo`; a proof that says `unfold_all` needs the
right spelled out. When that becomes the binding constraint, the answer is a
two-sided form — `proof p = lhs(T) rhs(U);`, normalizing both and requiring them
to meet — and nothing in the design blocks it.

### Where a proof lives

One `.hant` beside each `.hana`, checked as a bijection in both directions.

| the `.hana` | the sibling `.hant` |
|---|---|
| states identities, no `.hant` | error, listing what it must prove |
| states identities, `.hant` present | must prove exactly those, no more and no fewer |
| states none, `.hant` present | error — a renamed `.hana` orphans its proofs, and nothing else would notice |
| states none, no `.hant` | fine, which is nearly every file |

The rule governs where a proof is *declared*, not what it may reference. That
distinction is deliberate: when a proof may cite an identity stated in another
file — which is the point of building up a library of them — nothing about this
changes.

### Tactic definitions are file-local

A `tactic` defined in one `.hant` is invisible to every other. A proof has to be
readable beside the identity it proves, and a name that could have come from any
of a dozen files is not. A corpus-wide prelude is `prove --tactics <file>`,
which is the same mechanism said out loud.

A **tactic** name shadows, because the prelude is meant to be overridable. A
**proof** does not: a claim discharged twice was discharged once too often, and
that is an error naming both.

### One thing a `.hant` can do that a `--tactics` file cannot

A term in a `.hant` may name a sentence — `share { jump helper }` works in a
proof, and in a tactic defined beside it. That is not a special case but a
consequence of *when* each is read: a `--tactics` file is loaded before a corpus
is chosen, and a `.hant` only ever after one.

## What `prove` checks

Per identity, in order:

1. **Both sides** are non-recursive and unable to fail. Both, not only the side
   that gets rewritten: the right-hand side is the term the claim is measured
   against, so it has to be one the equations can speak about too.
2. The proof compiles, against its own file's definitions.
3. The tactic runs on the left-hand side.
4. **A miss fails it.**
5. The result equals the right-hand side by `same_effect_seq`, not by `==`.
6. The script **replays**: applying it to a fresh build reproduces the run
   exactly. Here `==` *is* right, and is the stronger claim — a replay that
   merely had the same effect would not be the same construction. This is what
   makes a derivation a derivation rather than a log written alongside one.

### Two deliberate differences from `rewrite`

Both are the same difference: `rewrite` explores, and `prove` decides.

- **A miss fails a proof**, where in `rewrite` it is a diagnostic that still
  prints the tree. `at(9, sink)` is a claim that there is something at 9; when
  there is not, the proof is aimed at a tree it no longer describes, and that is
  wrong even where the goal happened to be reached anyway. `try(...)` is how a
  proof says a miss is acceptable.
- **`--check` is on by default**, and `--no-check` turns it off. In `rewrite` it
  is opt-in because the listing is the answer and the check only costs time.
  Here the answer is *yes* or *no*, and a wrong yes is worse than a slow run.

### The failure output is the point

```
identity a_value_tested_twice ... FAILED

  the proof ran, but did not reach the right-hand side.

  proof: all
   --> tests/identities.hant:2

    what it reached            ┃   the right-hand side
  ─────────────────────────────╂─────────────────────────────
    ⋮ 2 unchanged lines        ┃
    0 │      1 │ branch then { ┃   0 │      1 │ branch then {
    0 │      0 │   push 1      ┃   0 │      0 │   push 1
      │        │ } else {      ┃     │        │ } else {
  - 0 │      0 │   push 4      ┃ + 0 │      0 │   push 3
      │        │ }             ┃     │        │ }
```

Two things had to be split apart to get that down to the line that matters.
`render_body` carries a header — index, name, annotations — which differs
between two sentences and would open every diff with two lines that always
disagree; `render_nodes` is the listing without it. And a `<inline>` label says
which sentence phase 4 put a block in, which never matches across two sentences,
so a listing being compared suppresses provenance the way `same_effect` already
ignores it. A `Call`'s label stays either way: there the target *is* the term.

### Exit codes

`0` every identity proved. `1` a claim is unproved, unproven, orphaned or
missing. `2` the corpus would not build, or the arguments were wrong. Three
rather than two because in CI those want different reactions.

## The corpus states four

`tests/identities.hana` already checked the rewriter's axioms *by executing
both sides on sample values*. It now states some of them as identities too, so
the same file answers two different questions: does the law hold on these
values, and does the rewriter's own equation set reach it.

Two of the four are worth reading for what they demonstrate rather than for what
they claim.

**`copying_a_constant`** — `push c ; pick 0` = `push c ; push c`. The proof
never uses the `copy_const` matcher, which would answer in one step. It reads
naturality backwards to put the second `push` inside a frame and then takes the
frame away, which is the argument that `copy_const` is a lemma and not an axiom.

**`discarded_work_on_copies`** — compute on copies, discard the results, and the
originals were never touched. It is the law that looked essential and turned out
to be derivable: one annihilation and two counits. It is also the identity whose
two sides need different amounts of stack, which is why an identity is held to
its net change.

Both had lived as Rust tests that ran a derivation by hand
(`applier::tests::copy_const_is_derivable_from_copy_nat`,
`vacuous_is_derivable_from_annihilate_and_counit`). Those stay — they check
something else, that the derivation is reversible step for step — but the claims
themselves are now in the language.

## What is not here yet

- **Identities as rewrite rules.** The point of writing claims down is to build
  on them: a proven identity should be citable in another proof, so a `.hant`
  can reach for a library of statements rather than for the axioms every time.
  The shape is a `StepKind::Identity { id }` beside `Unfold`, whose `sides()`
  regenerates both from the library; a matcher `identity(<path>)` whose width is
  the left-hand side's node count; and — unlike `unfold`, whose backward reading
  is the known gap because a window does not say which sentence to fold into —
  a free `inverse()`, since an identity's other side is written down.
- **Acyclicity.** With that in place a proof of A could cite B whose proof cites
  A. `prove` already collects every proof before checking any, which is where
  the topological order goes.
- **A trust boundary to write down.** Once `identity(...)` is a matcher,
  `rewrite -t 'each(identity(foo))'` will rewrite by a claim nobody has proved.
  Soundness comes from `prove`'s whole-corpus pass, not from the applier —
  which is an accepted asymmetry, `rewrite` being a debugging aid whose output
  does not even parse.
- **Two-sided proofs.** See "One-sided", above.
- **Scripts as files.** `docs/tactics.md` wants a derivation to be a saved
  value. A `.hant` saves the *tactic* that finds one, which is a smaller thing
  and needs no grammar for node sequences; the script form is still ahead.
