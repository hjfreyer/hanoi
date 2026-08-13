# Derivations

A **derivation** is a rewrite script written down: which equation to use, with
which arguments, in which direction, at exactly which place, one step per line.
`bin/replay` takes a file of them and decides whether they discharge the
identities they name.

```bash
cargo run --bin prove -- tests --emit derivations.hand   # find them
cargo run --bin replay -- tests derivations.hand         # check them
```

```
Checking 5 derivations...
identity identities::testing_a_test ... ok (2 steps)
identity identities::a_value_tested_twice ... ok (6 steps)
identity identities::copying_a_constant ... ok (3 steps)
identity identities::discarded_work_on_copies ... ok (3 steps)
identity identities::testing_a_test_by_name ... ok (3 steps)

derivation result: ok. 5 passed; 0 failed
```

## Why there is a format

Everything in `docs/tactics.md` is about *finding* a rewrite. The tactic
language, the matchers, the combinators, the fuel — all of it exists to search.
None of it is needed to **check** one, because a step says where it goes and the
applier only has to look:

> Applying a step is deliberately not a search. The equation regenerates the
> side it expects to find, the window is compared against it, and anything short
> of an exact match is a failure rather than an invitation to look elsewhere.

Until this format existed, that asymmetry bought nothing: a script lived in
memory, so the only way to get one was to run the search that produced it, in
the process that produced it. Written down, the two jobs come apart. A
derivation can be found by a tactic, by a solver, by a program in another
language, or by hand — and one small tool decides.

That is what the format is designed for, and it is why it is a **text format
that names things** rather than a dump of the in-memory structure. Three things
a step holds in memory mean nothing outside the process that built it, and each
is dealt with:

| in memory | on the wire | why |
|---|---|---|
| `SentenceIndex` | the fully qualified name | an index is an offset into one assembly of one corpus |
| `Symbol` | its declared path, looked up on the way in | a symbol compares by an `id` minted during assembly |
| `Dip::origins`, arm labels | dropped | provenance is not part of a term's identity — nothing that reads a replayed tree consults it |

The writer refuses to emit a name that does not resolve back to the thing it
came from, rather than writing one that would silently mean something else
somewhere else.

## What a file looks like

```
// A derivation of `identities::testing_a_test`.
derivation 1;

proof identities::testing_a_test {
    bool_result(op = is_bool) -> @0;
    annihilate(x = { is_bool }, n = 1, m = 1) -> @0;
}
```

The conventional extension is `.hand`. Whitespace and newlines carry no
meaning; `//` runs to the end of the line.

**`derivation 1;`** is the format version, and it is required. A checker that
meets a version it does not know refuses the file rather than reading as far as
it happens to parse.

**`proof <identity> { ... }`** names the claim the steps discharge, and the
identity is resolved the way everything else is resolved: an exact fully
qualified name, or an unambiguous trailing part of one. The steps carry that
identity's left-hand side to its right-hand side. A file may hold as many blocks
as it likes.

### A step

```
annihilate(x = { equal }, n = 2, m = 1) -> [1.then, 2.body] @2;
```

- **the equation**, by the name `--list-rules` and `docs/tactics.md` use;
- **its arguments**, named rather than positional — a wire format is read by
  someone debugging a generator that got one of them wrong, and `n = 2, m = 1`
  says which number is which where `2, 1` needs the reader to know;
- **the direction**: `->` finds the left-hand side and leaves the right, `<-`
  the other way. Every equation is true both ways and a step says which reading
  it wants;
- **the location**: `[1.then, 2.body]` is "the then arm of the node at index 1,
  then the body of the node at index 2 within it", read outermost-first, and
  `@2` is where the window starts in the sequence that walk arrives at. A bare
  `@0` is a window in the root sequence.

The direction and the location are spelled exactly as `--show-script` spells
them, so a step read off a listing and a step read out of a file are the same
text.

### Arguments, by equation

| equation | arguments |
|---|---|
| `collapse` | `k`, `j`, `a` |
| `elim_dip0` | `a` |
| `interchange` | `x`, `framed`, `n`, `m` |
| `fuse` | `k`, `a`, `b` |
| `hoist` | `k`, `x`, `then`, `else` |
| `distribute` | `then`, `else`, `suffix` |
| `fold_branch` | `c`, `then`, `else` |
| `eval` | `op`, `inputs` |
| `annihilate` | `x`, `n`, `m` |
| `commute` | `op` |
| `split_bool` | — |
| `counit` | `d` |
| `counit_under` | — |
| `retest` | `arm`, `inner`, `rest`, `other` |
| `copy_const` | `c` |
| `copy_assoc` | — |
| `copy_nat` | `x`, `n`, `m` |
| `bool_result` | `op` |
| `cancel_tuple` | `n` |
| `swap_cycle` | — |
| `unframe` | `framed`, `n`, `m` |
| `unfold` | `depth`, `target` |

Each equation's law is stated in `docs/tactics.md`, and its arguments are the
letters that law is written with. An argument is one of:

- **a count or a number** — `k = 2`, `n = -1`;
- **a term**, in braces — `x = { push 9 copy }`. Where an equation takes a
  single node the term holds exactly one: `framed = { dip 1 { drop } }`;
- **a literal** — `c = 9`, `c = true`, `c = "text"`, `c = 1.5`, `c = (1, 2)`,
  or a symbol by its declared path, `c = barista::state::thirsty`;
- **a list of literals**, in brackets — `inputs = [1, 2]`;
- **an instruction** — `op = is_bool`, `op = untuple 2`;
- **an arm** — `arm = then` or `arm = else`.

`unfold` is the one step that is not an equation of the calculus: that
`Call { k, S }` may be replaced by `S`'s body is the axiom the *library*
contributes by defining `S`. So it names a sentence and never quotes it —
`unfold(depth = 0, target = identities::drop_and_true)` is three words whether
the body is one instruction or ten thousand.

### Terms

A term is the same small language a tactic writes a term in — see
`docs/tactics.md` — with two additions a derivation needs and a hand-written
tactic did not:

```
{ copy is_bool branch { push true } { push false } }
{ dip 2 { push 9 add } }        a block, written out
{ dip 2 queue::accept }         a call that hides two values
{ jump queue::accept }          the same at depth 0
{ push (1, 2) }                 tuples
{ pick 2 }                      the frames a reach at depth stands for
```

`pick d` and `roll d` are spellings, not instructions: reading one gives the
frames around `copy` or `swap` that the compiler would have emitted, so a term
written either way is the same term. Nothing *writes* them — the tool has no
depth left to write — but a producer in another language may, and the two term
languages are meant to be one.

Every instruction has a spelling. Three once did not — `panic`, `assert` and
`assert_eq`, the three that could fail — since every equation here is stated
about code that cannot fail. They are gone from the language, so the exception
is too.

## What `replay` checks

Everything `prove` checks of its own derivation, in the same code:

- **every step applies**: the descent reaches a real node of a kind that has the
  part named, the window is in range and matches what the equation regenerates
  (compared by effect), the equation's side conditions hold against *this*
  library, and the replacement leaves the stack as the window did;
- what the last step leaves is the right-hand side, compared by effect.

**Nothing about being written down makes a step trusted.** Facts that originate
in the library ride in the arguments — the claimed arity of `X` in `interchange`
and `annihilate` — and are re-derived against the real program on every
application. A file claiming `add` is `(1 -> 1)` is refused however it came to
be written:

```
identity identities::testing_a_test ... FAILED

  a step does not fit.

  step 1 (annihilate -> @0): the step claims arity (1, 2) but the library says (1, 1)

  A location addresses the tree as the steps before it left it,
  so the step that stopped fitting is where the derivation and
  the library parted company — not necessarily where the
  mistake was made.

   --> derivations.hand:6:5
    |     annihilate(x = { is_bool }, n = 1, m = 2) -> @0;
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

What `replay` does *not* have is a tactic compiler, a matcher, a traversal, or a
fuel budget — a file is finite, so there is nothing to bound. The trusted
surface a producer has to be measured against is a parser and the applier, and
keeping it that small is the point.

`--complete` adds the other question: that every identity the corpus states is
derived by one of the files given. That is a question about the corpus rather
than about any one derivation, which is why it is a flag — sound but partial is
a perfectly good answer to "is what arrived correct?" and a bad one to "is
everything proved?".

## Writing a producer

`prove --emit <file>` is the reference: it writes out every derivation it
proved, and `./run_proofs.sh` runs both halves in sequence, so the format is
exercised end to end on every commit — found by the tactic engine, checked by
the replayer with the engine taken away.

A producer in another language needs to emit text and nothing else. It does not
need to link this crate, parse `.hana`, or agree with anything about how a
search should work; it needs the equation names, the argument names in the table
above, and the location syntax. What it does *not* have to get right is
soundness — a wrong derivation is refused at the step that is wrong, with a
line and a column.

Two things are worth knowing when writing one:

- **A location addresses the tree as the preceding steps left it.** Locations
  are not stable across a derivation: step 5 may name an index that did not
  exist when step 4 was written. That is not a defect but the reason a
  derivation is cheaper than a search.
- **Provenance is not part of a term's identity.** Origins never appear in the
  format, and a term is compared by effect, so a producer never has to know
  which `SentenceIndex` an inline block was given.

## See also

- [docs/tactics.md](tactics.md) — the equations, what each one's arguments mean,
  and the language for *finding* a derivation.
- [docs/identities.md](identities.md) — stating the claim a derivation
  discharges.
