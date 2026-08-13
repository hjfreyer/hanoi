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
| type checks | `TypeCheckPath(Path)` | `Dip(0, idx)`, or `Push(v); Equal` |
| calls | `Jump`, `Dip` | `Dip` only — `jump` is `Dip(0, idx)` |
| deep drops | `Drop(d)` | `Dip(d, idx)` around a plain `Drop` |
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
- `TypeCheckPath(path)` resolves to `Dip(0, idx)` for a predicate sentence, or
  `Push(v); Equal` for a path that names a value.

Resolution is `ModuleTree::resolve(scope, path)` — one entry point, one set of
rules, for every path in the language.

Phase 5 then runs `check_arities` over the resulting `Library`, followed by
`check_totality` and `check_identities`. A Z3-backed
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
values through an ADT constructor and a *partial* accessor, so it introduces
panic branches the verifier has to discharge; `dip` cannot. What a user can
write by hand is something with the same stack transition, not the same
construct.

Being core, `dip` needs nothing from phase 2 — sentence bodies pass through
lowering untouched — and phase 4 resolves its target exactly as it resolves
`jump`'s, including flattening an inline block into a fresh sentence.

### What phase 4 folds into it

Two core instructions have no bytecode of their own; phase 4 emits a `Dip` for
each. Note this is the *other* direction from `TypeCheckPath`, which is one
core instruction with two bytecode forms — there was never a rule that the two
vocabularies correspond one to one.

- **`jump S` becomes `Dip(0, idx)`.** A plain call is a dip whose hidden region
  is empty. The point is not the saved variant, it is that a traversal of the
  ISA can no longer handle one call instruction and silently miss the other —
  and one of the traversals that would have missed it is arity inference, which
  is what refuses recursion.
- **`drop d` for `d > 0` becomes `Dip(d, idx)` around a plain `Drop`.** Dropping
  at a depth was the only instruction that removed a value from the *middle* of
  the stack. With it gone, `Pick` and `Roll` are the only instructions that
  address below the top, which makes "this instruction crosses a frame" a
  two-case question rather than a four-case one.

`pick d` and `roll d` decompose the same way — `roll d` is
`dip { roll (d-1) }; roll 1`, and `pick d` is `dip { pick (d-1) }; roll 1`, so
`{dup, swap, drop, dip}` generates every shuffle in the language. **Do not take
that trade.** It replaces one instruction with `O(d)` instructions and `O(d)`
calls, and each expansion still bottoms out in a frame-crossing `roll 1`, so
the hard case is multiplied rather than removed. A minimal primitive set makes
the metatheory smaller and the analysis larger; here the analysis is the point.

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
