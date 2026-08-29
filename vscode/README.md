# Hanoi for VS Code

Syntax highlighting and editing support for Hanoi Assembly (`.hana`) and the
tactics language proofs are written in (`.hant`).

## What it does

**Highlighting.** Both grammars are TextMate grammars derived from the real
lexer — the keywords in `lang/bytecode/src/assembly.rs`, the instruction table in
`parse_instruction`, the composers in `Composer::from_name`, and the steps and
tactics in `lang/rewrite/src/hant.rs`. A word the assembler does not know is not
highlighted as one.

The declaration keywords (`sentence`, `function`, `mod`, `symbol`,
`const_string`, `type`, `enum`, `identity`) each scope the name that follows
them, so a declaration reads as the thing it names. `type` specs and `enum`
bodies are their own context, which is what lets `int`, `bool`, `symbol`,
`tuple` and `const_string` read as primitive type names there and as
instructions or keywords everywhere else. Paths are scoped a segment at a
time: `crate` and `super` as roots, interior segments as modules, and the leaf
as what it is.

`mod` is both a declaration keyword and the alias for `modulo`. It reads as a
declaration only when a name follows it on the same line, which is exactly
when it is one.

A box address — the `#nkz` an `at` step names a box with, which a proof
copies out of a failed run's listing — reads as a constant. The letters are
`k` through `z` and nothing else, which is what tells one from every other
word in the file.

**Comments.** `//` to end of line is the only comment the language has, so
that is the only one configured: `Ctrl+/` toggles it, and *Toggle Block
Comment* falls back to it rather than inserting a `/* */` the lexer would
reject. Pressing Enter inside a comment continues it.

**Editing.** Bracket matching and auto-closing for `{}`, `[]`, `()` and `"`,
indentation that follows the braces, and snippets for the declaration forms
(`sentence`, `function`, `test`, `branch`, `dip`, `mod`, `enum`, `type`,
`identity`).

## Installing

The extension is plain JSON — there is nothing to build.

**For local development**, symlink it into the extensions directory and
restart VS Code:

```sh
ln -s "$PWD/vscode" ~/.vscode/extensions/hanoi
```

**To package it** as a `.vsix`:

```sh
npx @vscode/vsce package
```

Then *Extensions → … → Install from VSIX…*, or `code --install-extension
hanoi-0.1.0.vsix`.

## Checking a change to the grammar

The grammars were checked by tokenizing every `.hana` and `.hant` file in the
tree — the `hana/` corpus and the compiler's templates under `lang/` — and
looking at what came back: both which scopes were assigned and which text fell
through every rule. To repeat that after a change:

```sh
npm install vscode-textmate vscode-oniguruma
```

and tokenize with `vscode-textmate`, loading `syntaxes/*.tmLanguage.json` by
scope name (`source.hana`, `source.hant`). Text left with only the root scope
is text no rule claimed; today that is bare operand identifiers — a symbol
being pushed by name, a module named as a composer argument — and the `{{...}}`
placeholders in `lang/bytecode/src/templates/*.tmpl.hana`, which are not Hanoi.
