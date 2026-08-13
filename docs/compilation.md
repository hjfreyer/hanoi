# Compilation pipeline

This document specifies the representations a Hanoi program passes through and
what each phase is allowed to assume.

```
text ──0──> tokens ──1──> sugar AST ──2──> core AST ──3──> module tree ──4──> Library
          tokenize      parse        lower        declare        resolve+emit
```

## Is core the same as bytecode?

No. They are separated by two erasures, and the difference is worth stating up
front because it determines where the core/sugar seam goes.

The test for whether something belongs in **core** is: *could a user have
written this by hand in `.hana` source?* Core is the subset of the surface
language that cannot be expressed in terms of other surface constructs. A user
can write `mod`, `symbol`, `const_string`, `sentence` longhand, so those are core. A user cannot
write a `SentenceIndex`, so bytecode is not core.

| | core AST | bytecode (`Library`) |
|---|---|---|
| structure | nested modules | flat `TiVec<SentenceIndex, Sentence>` |
| references | `Path` (names) | `SentenceIndex` (indices) |
| constants | `Ref(Path)` | `Value::Symbol { id, path }`, `Value::ConstString(text)` |
| branch targets | `Target::Label` or inline block | `SentenceIndex` |
| type checks | `TypeCheckPath(Path)` | `Jump(idx)`, or `Push(v); Equal` |
| calls | `Jump`, `Dip(N)` | `Jump(idx)` and `Dip(idx)` — a frame hides one value, and `N` of them is that many nested |
| movement at depth | `Drop(d)`, `Pick(d)`, `Roll(d)` | frames around `Drop`, `Copy` and `Swap`; no instruction takes a depth |
| `?` | `Try` | `Untuple(2)` and two `Branch`es, the rest of the block in an arm |
| declarations | `symbol`, `const_string`, `mod` | erased |
| annotations | attached to the sentence | side table keyed by `SentenceIndex` |

The two erasures are different in kind:

- **sugar → core** erases *abbreviation*. Everything it removes, the user could
  have typed out longhand. It is purely syntactic.
- **core → bytecode** erases *names and nesting*. This one cannot be run
  backwards into source, and it requires name resolution.

Keeping them distinct is what lets phase 4 assume every name it sees is one a
user could have written, rather than one a desugaring invented.

## Phase 0: tokenize

`text -> Vec<Token>`. Strips whitespace and `//` comments; recognizes the
keyword set (`export`, `symbol`, `const_string`, `test`, `mod`, `sentence`,
`function`, `type`, `enum`, `true`, `false`) and the punctuation used by paths, annotations, blocks
and tuples.

Note that `crate` and `super` are *not* keywords here — they tokenize as
identifiers and are classified during path parsing. This is why `mod crate {}`
reaches the declaration check rather than failing in the lexer.

**Known gap:** the tokenizer tracks a line number for error messages but does
not attach it to tokens, so every phase after this one reports errors without a
source position.

## Phase 1: parse

`Vec<Token> -> sugar::Module`. The only non-syntactic work is file module
inclusion: `mod name;` reads `name.hana` relative to the current base directory
and parses it as the module body. That is source acquisition, so it belongs
here rather than in lowering.

**This phase performs no desugaring.**

### sugar AST

```rust
pub struct Module {
    pub items: Vec<Item>,
}

pub enum Item {
    Symbol(SymbolDecl),           // core
    ConstString(ConstStringDecl), // core
    Sentence(SentenceDecl),  // core
    Identity(IdentityDecl),  // core
    Mod(ModDecl),            // core
    Type(TypeDecl),          // sugar
    Enum(EnumDecl),          // sugar
    Compose(ComposeDecl),    // sugar
}

pub struct TypeDecl {
    pub name: String,
    pub spec: TypeSpec,
    pub annotations: Vec<Annotation>,
}

pub struct EnumDecl {
    pub name: String,
    pub variants: Vec<EnumVariant>,   // name + payload element specs
    pub annotations: Vec<Annotation>,
}

pub struct ComposeDecl {
    pub name: String,
    pub composer: Composer,           // an enum, not a String
    pub args: Vec<ModuleExpr>,        // may nest further composers
    pub is_test: bool,
}

pub struct ModDecl {
    pub name: String,
    pub items: Vec<Item>,             // sugar::Item
    pub is_test: bool,
}
```

`SentenceDecl` carries `is_exported`, `is_test`, `annotations`, and a body; the
`function` keyword is represented by a flag on it, not a separate variant.

Two notes on this shape:

- `Composer` should be an enum, not the current `String` plus
  `is_composer_name` string comparison. Arity and argument-kind checking then
  moves to lowering with an exhaustive match.
- `TypeSpec` (`Primitive | Literal | Path | Tuple | Union`) is a sugar-only
  type. It never appears in core.

## Phase 2: lower

`sugar::Module -> core::Module`. Purely syntactic, position independent, and
requires **no module tree and no scope**. It needs exactly one piece of mutable
state: a counter for naming anonymous composer modules.

### The depth rule

Every lowering places its output one or more levels *deeper* than the
declaration the user wrote (`type Pair …;` becomes `mod Pair { sentence check
}`). Paths are therefore split by authorship:

- **User-written paths** — a type spec's `MyOther`, a composer's arguments —
  were written relative to the *declaration site*, so the lowerer shifts them by
  the output depth (prepend one `super` per level, unless already `crate`-rooted).
- **Lowerer-generated paths** are emitted relative to the *landing site*
  directly, with no compensation.

The lowerer knows its own output depth by construction, which is why it needs
nothing from the tree.

The depth is **per lowering, not a constant**: a `type` check lands one level
deep, composer arguments shift by one, and an enum's `Body::check` lands three
(`Name` / `Variant` / `Body`). Applying this uniformly removed both of the
earlier workarounds — `adjust_path`, which shifted paths for composers only,
and `is_type_check`, which instead shifted the *resolution scope* for type
checks only. Those used to cancel each other, which forced the enum lowering to
emit `Case1::tag` and `MyEnum::Case1`; those leading segments existed purely to
undo the scope shift, and are now plain `tag` and `Case1`.

It also lifted a real restriction. Under the old scope shift a variant payload
could not name a sibling by a relative path at all — `enum E { A(Small) }`
failed with *"Item 'Small' not found in module 'crate::E::A'"*, which is why
`tests/queue.hana` spells out `crate::queue::Elem` in every payload. Relative
payload paths now resolve, and `type_tests.hana` pins the behavior.

### The lowerings

| sugar | core |
|---|---|
| `function f { … }` | `sentence f { … }` + `Annotation::Arity(1, 1)` |
| `type N spec;` | `mod N { export sentence check { …spec… } }`, `Total` added if absent |
| `enum N { V(specs), … }` | `mod N { mod V { symbol tag; mod Body { check }; check }, …; check }` |
| `mod m compose_X(args);` | `mod m { …template items… }`, plus sibling `__anon_mod_N` for nested composers |

`enum` lowers **directly to core**, reusing the same helper functions the
`type` lowering uses. It does not lower to a `TypeDecl` first. This keeps the
lowering graph a star rather than a chain, so there is no ordering between
lowerings and no fixpoint to reason about.

**Invariant: sugar never lowers to sugar.** The first new construct that looks
like "an enum with extra steps" will tempt you to break this; don't.

### core AST

```rust
pub struct Module {
    pub items: Vec<Item>,
}

pub enum Item {
    Symbol(SymbolDecl),
    ConstString(ConstStringDecl),
    Sentence(SentenceDecl),
    Identity(IdentityDecl),
    Mod(ModDecl),   // items: Vec<core::Item>
    Use(UseDecl),   // see below
}
```

`SymbolDecl`, `ConstStringDecl`, `SentenceDecl` and `IdentityDecl` are shared verbatim with sugar. `ModDecl` is
duplicated only because its child type differs. Instruction bodies, values,
paths and annotations are all shared. **The seam is one 8-variant enum against
one 6-variant enum, and one struct** — everything else is shared by
composition. That is the entire cost of the split, and it is why parallel ASTs
per conceptual level are not worth it: enum → type → predicate is three
concepts but only two vocabularies.

## Phase 3: declare

`core::Module -> ModuleTree + Vec<(ModuleId, SentenceDecl)>`. This is today's
`TreeBuilder` with the lowering removed. It:

- allocates a `ModuleId` per module and a `SentenceIndex` per sentence,
- binds every name via `declare`/`declare_module`, which reject reserved words
  and redeclarations against the single per-module namespace,
- assigns symbol ids and the fully qualified path each symbol prints as,
- populates the `exports`, `tests` and `test_machines` maps by fully qualified
  name,
- checks that a `test mod` has an `init` sentence, and for composed test
  machines exports the seven machine sentences.

Each sentence is paired with the `ModuleId` its paths resolve against. Because
phase 2 applied the depth rule, that scope is always simply *the module the
sentence is declared in* — no special case for type checks.

## Phase 4: resolve and emit

`ModuleTree + sentences -> Library`. For each sentence body, against its scope:

- `ParsedValue::Ref(path)` resolves to a `Value` — a symbol or a const string,
- `Target::Label(path)` resolves to a `SentenceIndex`,
- `Target::Inline(body)` is flattened into a freshly allocated sentence,
- `TypeCheckPath(path)` resolves to `Jump(idx)` for a predicate sentence, or
  `Push(v); Equal` for a path that names a value,
- `pick d`, `roll d`, `drop d` and `dip N` lose their depths, expanding into
  the core recursion — see [what phase 4 folds into it](#what-phase-4-folds-into-it).

Resolution is `ModuleTree::resolve(scope, path)` — one entry point, one set of
rules, for every path in the language.

Phase 5 then runs `balance_early_returns` — the one thing phase 4 leaves unfinished,
see below — followed by `check_arities`, `check_totality` and `check_identities`. A Z3-backed
precondition/postcondition/total checker previously ran separately via
`bin/typecheck`; it has been removed from the codebase for now (see
[docs/typecheck.md](typecheck.md) for the design).

## Where `dip` fits

`dip` is **core**, and the reason is worth recording because it is the first
construct where the "could a user have written this by hand?" test gives the
wrong answer on its own.

A user *can* write the longhand — `tuple k`, roll the block's arguments over
the packed value, run the block, roll the packed value back, `untuple k` — so
the test appears to say sugar. But the roll counts depend on the block's own
arity, and arity inference does not run until phase 5, two phases after
lowering. A lowering that needs information phase 2 cannot have is not a
lowering.

The semantics are not expressible either. The longhand routes the hidden
values through an ADT constructor and a *fallible* accessor, so it introduces a
flag per hidden value and a junk answer to discharge; `dip` cannot. What a user can
write by hand is something with the same stack transition, not the same
construct.

Being core, `dip` needs nothing from phase 2 — sentence bodies pass through
lowering untouched — and phase 4 resolves its target exactly as it resolves
`jump`'s, including flattening an inline block into a fresh sentence.

### What phase 4 folds into it

Several core constructs have no bytecode of their own; phase 4 emits the
instructions they stand for. Note this is the *other* direction from
`TypeCheckPath`, which is one core instruction with two bytecode forms — there
was never a rule that the two vocabularies correspond one to one.

- **`?` becomes `Untuple(2)` and two branches.** The rest of the block moves
  into the arm that runs when the tag was `crate::prelude::ok`, and the other
  arm rebuilds the error and ends there. See [docs/hana.md](hana.md#the--operator)
  for the shape and why it cannot fail.
- **`dip N { ... }` becomes `N` nested one-deep frames.** `dip 0` is a `Jump`
  and `dip 1` is a `Dip`; anything deeper is a `Dip` around a block holding the
  frame one shallower. The chain is shared per (depth, target), so a sentence
  dipped to twice is wrapped once.
- **`pick d`, `roll d` and `drop d` become frames around `copy`, `swap` and
  `drop`.** One recursion, three ways, parting where there is nothing left to
  reach past:

  ```text
  drop 0 = drop            pick 0 = copy               roll 0 = ε
  drop d = dip { drop (d-1) }
  pick d = dip { pick (d-1) } ; swap
  roll d = dip { roll (d-1) } ; swap
  ```

  The trailing `swap` brings the answer up from under the value the frame hid,
  and `drop` has none because it leaves nothing to bring. `roll 1` is written
  directly rather than through the recursion, which would call a block holding
  nothing. One block per (reach, depth) is shared by every site that expands to
  it, so a program pays for one chain per depth rather than one per mention —
  and `vm::movement_tests` measures the expansion against the semantics it
  replaced, at every depth up to seven and every stack size that fits.

### Why the depths go, and what it costs

A depth on an instruction is a **pointer into the stack**. A frame's width was
one too. Every law about either is an infinite family indexed by that pointer,
with arithmetic in its side conditions, and five of the rewriter's axioms
existed only to say things about `pick d` and `roll d` that `copy`, `swap` and
a one-deep `dip` say in a single equation each. `pick_roll` was the definition
the compiler now performs; `roll_cycle` became `swap ; swap` = nothing;
`collapse` stopped being how a term arrives and became a rewrite that a proof
asks for. A frame's width is now a *shape* — how many frames — which no
analysis can get wrong and no equation does arithmetic on.

**This document used to argue the other way**, and the argument is worth
recording because half of it was right:

> `pick d` and `roll d` decompose the same way […] so `{dup, swap, drop, dip}`
> generates every shuffle in the language. **Do not take that trade.** It
> replaces one instruction with `O(d)` instructions and `O(d)` calls, and each
> expansion still bottoms out in a frame-crossing `roll 1`, so the hard case is
> multiplied rather than removed. A minimal primitive set makes the metatheory
> smaller and the analysis larger; here the analysis is the point.

The occurrences are multiplied; the *cases* go to one. An analysis pays per
case — per rule variant, per match arm, per side condition, per instance of a
family it has to be right about — and soundness risk scales with axiom families
rather than with node count. The `O(d)` is real and small: across the corpus,
96% of movement is already at depth ≤ 1, the deepest thing anyone has written
is `pick 5`, and the shared blocks mean the whole program pays for about five
chains rather than one per site.

What the argument got right is that the expansion **creates frames**, and a
frame is what the rewriter sees through worst — it is the reason `unframe` had
to be assumed. A `pick 2` that was one visible node is now a `swap` behind two
frames, and reaching it means opening them first. Two places in the corpus paid
for that directly: an aimed `annihilate` in `discarded_work_on_copies`, because
an unaimed one now reads a wider window than it used to, and the positions in
the hand-written derivations that `speculate` and `bool_result_copied` stand
for, which count nodes and so count the expansion.

## Where `?` fits

`?` is **core**, for the same reason `dip` is, and it is the sharpest case of it.

A user can write the longhand — `untuple 2`, ask which tag it carries, put the
rest of the block in an arm — so the "could a user have written this by hand?"
test says sugar. But the arm that leaves early has to drop whatever the rest of
the block would have consumed, and *how many that is* is the arity of the rest
of the block. Phase 2 has no arities and no scope; it cannot even see that the
rest of the block calls something. A lowering that needs information phase 2
cannot have is not a lowering.

So phase 4 emits the whole shape, and leaves the failure arm one step short of
finished:

```
Untuple(2)
Branch(is_ok, not_a_result)          //  push ok equal   |   drop 0 push false
Branch(rest, fail)                   //  the rest of it  |   push err tuple 2
```

`balance_early_returns` then reads the arity of `rest` — a real sentence by now,
so `sentence_arity` answers — and appends `inputs - outputs` deep drops to
`fail`. It runs before `check_arities` because what it is doing is making the
two arms agree; run it after and the check it exists to satisfy has already
failed.

Two ordering facts hold it together:

- **Every sentence has been emitted**, so the arity of a `rest` arm that calls
  something is knowable. This is what phase 4 could not say.
- **Sites arrive innermost first.** A `?` nested inside another's `rest` arm is
  balanced before that arm is measured; until it is, its own two arms disagree
  and the arm has no arity to read.

A rest arm that *leaves* more than it takes is refused: an early return would
have to invent the difference. So is a program that uses `?` without declaring
the tags it reads.

## Where `identity` fits

`identity A = B` is **core**, and it is the second construct where the
"could a user have written this by hand?" test needs an argument rather than an
inspection. A `sentence` names code and a `test sentence` runs it; neither
states an equation, and there is no combination of surface constructs that does.
A hypothetical lowering to two sentences plus *something* leaves the *something*
with nowhere in core to live, so the lowering buys nothing. It lowers to itself.

Phase 3 declares the name into the module's one namespace as
`ModuleItem::Identity`, so `identity foo` and `sentence foo` collide and a
fully qualified identity name denotes exactly one thing. It allocates two
`SentenceIndex`es and pushes two `SentenceDecl`s named `foo::lhs` and `foo::rhs`
— **in lockstep**, since phase 4 relies on `flat_sentences[i]` being
`SentenceIndex(i)`.

Phase 4 needs no special case at all, which is the interesting fact: the two
sides compile exactly as any named sentence does, inline blocks and all.

`IdentityDecl` is the one AST node that carries a `Span`, and it carries it as
*data*: an identity is proved in the file beside the one that stated it, so
which file that was has to survive into the `Library`. `SourceMap::path` is the
other half. Everything after parsing still reports errors against the module
tree.

## Where `use` fits

`use` is **core**, not sugar: it introduces a binding that cannot be expressed
in terms of other constructs. It is a `core::Item::Use` in phase 2's output, a
`ModuleItem::Use(Path)` binding in phase 3, and phase 4 follows it during
resolution — re-resolving the target path in the scope of the module that
*declared* the `use`, with a visited set for cycle detection.

Because resolution is a separate phase from declaration, `use` is
order-independent within a module for free; prefer that over Rust's
declaration-order rules.

## Open questions

- **Inline blocks.** `branch { … } { … }` and `dip N { … }` are surface syntax
  and could be lowered in phase 2 into named sentences. Recommendation: keep
  them in core and flatten in phase 4. Lowering them early requires inventing
  names in the module namespace for something that is genuinely anonymous;
  phase 4 already allocates sentence indices and handles it naturally.
- **`TypeCheckPath` and the `::check` fallback.** Phase 4 currently tries the
  path, then retries with `::check` appended, discarding the first error. This
  should be one explicit rule — "a path in type position denotes its `check` if
  it resolves to a module" — with a real error message.
- **Annotation paths.** `Precondition`/`Postcondition` currently hold `String`,
  are flattened at parse time, and are resolved by a separate resolver with
  different rules. They should hold `Path` and go through phase 4.
- **Anonymous module names.** `__anon_mod_N` must remain a legal identifier for
  as long as composer templates round-trip through text. Once phase 2 emits
  structured core items instead, the name can become unspellable.
- **Structured templates.** Composer templates are still rendered as text and
  re-tokenized, so their output has to be parsed back into sugar and lowered a
  second time. Parsing each template once, with holes, would remove the round
  trip and let anonymous module names become unspellable.

## Testing the phases

Give `core::Module` a pretty-printer and snapshot-test each lowering. This is
the cheap substitute for a type-level phase index: it makes "what does this
sugar mean" a readable diff, catches scope and depth bugs that types would not,
and doubles as documentation. The current text-template approach for composers
has this property by accident — don't lose it when the templates become
structured.
