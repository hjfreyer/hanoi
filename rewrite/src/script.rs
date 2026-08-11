//! The tactic script language: tokenizer, parser, and name resolution.
//!
//! ```text
//! script := def*
//! def    := "tactic"   ident "=" expr ";"
//!         | "strategy" ident "=" expr ";"
//!         | "proof"    path  "=" expr ";"      // .hant only
//! path   := ident ("::" ident)*
//! expr   := choice
//! choice := seq ("|" seq)*
//! seq    := prim (";" prim)*
//! prim   := ident | ident "(" args ")" | "(" expr ")"
//! arg    := int | expr | ident ":" expr
//! ```
//!
//! A `.hant` is this language with `proof` added: the file beside a `.hana`,
//! holding a proof of each identity that `.hana` states. A `--tactics` file is
//! the same language without it, since a claim discharged has nowhere to land
//! when there is no corpus to state it.
//!
//! One grammar, two languages. A `tactic` transforms a term and a `strategy`
//! discharges a goal, and both are written with the same names, calls and `|` —
//! what differs is the table each is resolved against. A proof body is resolved
//! as a strategy, and one that names no strategy is resolved as a tactic and
//! read as [`Strategy::Blind`], so a `.hant` written before the third layer
//! existed means exactly what it always did. See [`crate::prover`].
//!
//! Two precedence levels, one more than the rest of the codebase has. Hand
//! written recursive descent, like the `.hana` parser.
//!
//! Every token carries a byte span, so an error can point at the offending
//! word instead of describing it. `.hana` spans its tokens the same way, but
//! against a `SourceMap` — it has many files to name, where this language has
//! only the prelude and whatever came in on the command line.

use std::collections::{HashMap, HashSet};

use bytecode::{Instruction, Value};

use crate::engine::Tactic;
use crate::ir::{Node, Selector};
use crate::matcher::{
    Matcher, count_matcher_names, matcher_by_name, matcher_names, matcher_with_count,
    matcher_with_term, term_matcher_names,
};
use crate::program::{Program, resolve_sentence, resolve_symbol};
use crate::prover::{Descent, Move, Strategy};

/// The named tactics every session starts with.
///
/// A tactic may not take a matcher's name, so where a pass and the matcher at
/// its heart would collide the pass is the one that gives way: `annihilation`
/// drives `annihilate`, `flattening` drives `flatten`.
pub(crate) const PRELUDE: &str = r#"
// Splice every call into its caller, all the way down, leaving one flat
// sentence. `each` alone already opens a whole sequence transitively, since an
// unfolded body is rescanned where it landed; the `bu` is what reaches into
// branch arms as well.
//
// For less than all of it, `once(unfold)` takes the first call only, and
// `repeat_n(k, once(unfold))` takes k of them.
tactic unfold_all = repeat(bu(each(unfold)));

// Nothing is opened unless you ask. The listing names every call on one line,
// and you unfold the ones you care about.
tactic default = id;

// Move framed blocks left, fuse the ones that meet, and keep nested frames
// collapsed so the interchange law sees a frame's true hidden depth.
tactic dips = repeat(bu(each(collapse); each(sink); each(fuse)));

// Split every frame into a nest of unary ones. Presentation only, and the
// opposite reading of the same law as `collapse` — never put both in one
// `repeat`.
tactic unary = repeat(bu(each(expand)));

tactic factoring = repeat(bu(each(factor)));

// Throw away results nothing reads. `annihilate` reads one output and
// `annihilate_flagged` two, which is what a fallible instruction leaves;
// `annihilate_void` reads none, which is what an empty branch is; `counit` is
// the copy that was made only to be discarded.
tactic annihilation =
    repeat(bu(each(annihilate, annihilate_flagged, annihilate_void,
                   counit, counit_under)));

// Evaluate what is already decided. Every matcher here answers a question about
// values rather than about shape, and the equation underneath declines anything
// it has no answer for — so `eval2` folds `equal` on any pair and simply does
// not fire on `add`.
tactic values = repeat(bu(each(eval1, eval2, bool_result, bool_result_copied,
                              cancel_tuple, copy_const)));

// Delete shuffles an operator cannot see. `comm` is the only law here and it
// strictly shrinks the term, so unlike its backward reading `swap` it is safe
// in a fixpoint.
tactic commuting = repeat(bu(each(comm)));

// Throw away work that does nothing, then fold what that exposes. The two
// belong together because each makes work for the other: folding is what
// produces the literal `fold_branch` needs, and deciding a branch is what
// exposes the next thing to fold.
// `retest` is here rather than with the branch passes because what it does is
// delete an arm that cannot run, which is cleanup by any reading.
tactic cleanup = repeat(bu(each(annihilate, annihilate_flagged, annihilate_void,
                                counit, counit_under, comm, fold_branch, retest);
                           each(eval1, eval2, bool_result, bool_result_copied,
                                cancel_tuple, copy_const)));

// Empty every branch arm of everything but `branch`, `drop` and `pick`, so
// that what is left of a branch is the choice it makes and none of the work it
// was doing. `factor` takes what both arms share and `lift` takes what one arm
// has — either way the computation ends up in front of the branch, where the
// laws that fold values can reach it and where two arms testing the same thing
// come to be testing the *same* node.
//
// Alternated with `dips` rather than run to a fixpoint first: every firing
// leaves a `dip 1 { X }` behind, and collapsing and sinking those is what
// lets the next one see a prefix rather than a pile of frames.
tactic lifting = repeat(bu(each(factor); each(lift);
                           each(collapse); each(sink); each(fuse)));

// Push what follows a branch into both of its arms, so a law that only holds on
// one side can see it. Kept out of `all` and `cleanup`: it duplicates code on
// purpose, which is the opposite of what those two are for.
tactic distribution = repeat(bu(each(distribute)));

// Splice plain calls into their call sites. This is what lets the other laws
// reach across a frame: a branch one level down and the instruction after the
// call are not in the same sequence until the frame is gone. It discards the
// origin labels, so it is opt-in rather than part of `all`.
tactic flattening = repeat(bu(each(flatten)));

// Everything that makes a term smaller, at once.
tactic all = repeat(bu(each(annihilate, annihilate_flagged, annihilate_void,
                            counit, counit_under, comm, fold_branch, retest);
                       each(eval1, eval2, bool_result, bool_result_copied,
                            cancel_tuple, copy_const);
                       each(factor);
                       each(collapse); each(sink); each(fuse)));

// Frames left-most and written in unary.
tactic dip_normalize = dips; unary;
"#;

pub(crate) type Span = (usize, usize);

#[derive(Debug)]
pub(crate) struct ScriptError {
    pub(crate) message: String,
    pub(crate) span: Span,
    pub(crate) help: Option<String>,
}

impl ScriptError {
    pub(crate) fn new(message: impl Into<String>, span: Span) -> Self {
        ScriptError {
            message: message.into(),
            span,
            help: None,
        }
    }

    /// A spanned error against a `.hant`, raised from outside this module.
    ///
    /// `prove` reports an orphan proof — one naming an identity that is not
    /// stated in the sibling `.hana` — and wants it to underline the path the
    /// way a parse error underlines a word.
    pub(crate) fn about(message: impl Into<String>, span: Span, help: impl Into<String>) -> Self {
        ScriptError::new(message, span).with_help(help)
    }

    pub(crate) fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Renders the error against the source, pointing at the span.
    ///
    /// The tactic came from the command line, so it has no file to name.
    pub(crate) fn render(&self, source: &str) -> String {
        self.render_in(source, "tactic")
    }

    /// The same, naming the file it came from — a `.hant`, or a `--tactics`
    /// file.
    pub(crate) fn render_in(&self, source: &str, name: &str) -> String {
        let (start, end) = self.span;
        let line_start = source[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
        let line_end = source[start..]
            .find('\n')
            .map(|i| start + i)
            .unwrap_or(source.len());
        let line_no = source[..start].matches('\n').count() + 1;
        let column = start - line_start;
        let width = (end.saturating_sub(start)).max(1);

        let mut out = format!("error: {}\n", self.message);
        out.push_str(&format!(" --> {}:{}:{}\n", name, line_no, column + 1));
        out.push_str(&format!("  | {}\n", &source[line_start..line_end]));
        out.push_str(&format!(
            "  | {}{}\n",
            " ".repeat(column),
            "^".repeat(width)
        ));
        if let Some(help) = &self.help {
            out.push_str(&format!("  = help: {}\n", help));
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Tokenizing
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    Int(usize),
    Str(String),
    Tactic,
    Strategy,
    Proof,
    Eq,
    Semi,
    Comma,
    Colon,
    Pipe,
    LParen,
    RParen,
    LBrace,
    RBrace,
}

struct Spanned {
    tok: Tok,
    span: Span,
}

fn tokenize(src: &str) -> Result<Vec<Spanned>, ScriptError> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;

    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // `//` to end of line, as in .hana.
        if c == '/' && bytes.get(i + 1) == Some(&b'/') {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        let start = i;
        let tok = match c {
            '=' => {
                i += 1;
                Tok::Eq
            }
            ';' => {
                i += 1;
                Tok::Semi
            }
            ',' => {
                i += 1;
                Tok::Comma
            }
            // Names a part of a `descend`. A lone colon only: `::` is glued
            // into an identifier by the word scanner below, so a path never
            // reaches here.
            ':' => {
                i += 1;
                Tok::Colon
            }
            '|' => {
                i += 1;
                Tok::Pipe
            }
            '(' => {
                i += 1;
                Tok::LParen
            }
            ')' => {
                i += 1;
                Tok::RParen
            }
            '{' => {
                i += 1;
                Tok::LBrace
            }
            '}' => {
                i += 1;
                Tok::RBrace
            }
            // A const string is written out, unlike a symbol: it is exactly its
            // text, so there is nothing to look up. No escapes, as in .hana.
            '"' => {
                i += 1;
                let text_start = i;
                while i < bytes.len() && bytes[i] != b'"' {
                    i += 1;
                }
                if i == bytes.len() {
                    return Err(ScriptError::new("unclosed string literal", (start, i)));
                }
                let text = src[text_start..i].to_string();
                i += 1; // consume the closing quote
                Tok::Str(text)
            }
            c if c.is_ascii_digit() => {
                while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                    i += 1;
                }
                let text = &src[start..i];
                let value = text.parse::<usize>().map_err(|_| {
                    ScriptError::new(format!("'{}' is too large a number", text), (start, i))
                })?;
                Tok::Int(value)
            }
            c if c.is_alphabetic() || c == '_' => {
                let word = |i: &mut usize| {
                    while *i < bytes.len() && {
                        let c = bytes[*i] as char;
                        c.is_alphanumeric() || c == '_'
                    } {
                        *i += 1;
                    }
                };
                word(&mut i);
                // `::` continues the same token, so a term can name a sentence
                // the way the command line does. Nothing else in this language
                // uses a colon, so there is no ambiguity to resolve.
                while src[i..].starts_with("::") {
                    i += 2;
                    word(&mut i);
                }
                match &src[start..i] {
                    "tactic" => Tok::Tactic,
                    "strategy" => Tok::Strategy,
                    "proof" => Tok::Proof,
                    word => Tok::Ident(word.to_string()),
                }
            }
            other => {
                return Err(ScriptError::new(
                    format!("unexpected character '{}'", other),
                    (start, start + other.len_utf8()),
                ));
            }
        };
        out.push(Spanned {
            tok,
            span: (start, i),
        });
    }

    Ok(out)
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// A tactic expression before names are resolved.
#[derive(Clone)]
enum Expr {
    Name(String, Span),
    Call(String, Span, Vec<Arg>),
    /// A matcher and the term it is completed by: `introduce { pick 0 }`.
    ///
    /// Every other matcher rewrites what it found, so what it produces is a
    /// function of the window. An introduction has nothing to read — the code
    /// it puts into the term has to be written down somewhere, and this is
    /// where.
    Term(String, Span, Vec<Node>),
    Seq(Vec<Expr>),
    Choice(Vec<Expr>),
}

#[derive(Clone)]
enum Arg {
    Expr(Expr),
    Int(usize),
    /// `then: cleanup` — a part of a `descend`, which is the one form whose
    /// arguments are not interchangeable.
    ///
    /// A branch decomposes into *two* goals and both have to be discharged, so
    /// naming them beats an order nobody would remember.
    Named(String, Span, Expr),
}

struct Parser<'a> {
    toks: &'a [Spanned],
    pos: usize,
    end: usize,
    /// Only needed to resolve a sentence named inside a term, and to work out
    /// the arity of one. A tactic that names no sentence compiles without a
    /// program, which is what keeps the prelude checkable on its own.
    prog: Option<&'a Program<'a>>,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|s| &s.tok)
    }

    fn span(&self) -> Span {
        self.toks
            .get(self.pos)
            .map(|s| s.span)
            .unwrap_or((self.end, self.end))
    }

    fn bump(&mut self) -> Option<&'a Spanned> {
        let out = self.toks.get(self.pos);
        if out.is_some() {
            self.pos += 1;
        }
        out
    }

    fn expect(&mut self, want: Tok, what: &str) -> Result<Span, ScriptError> {
        let span = self.span();
        match self.peek() {
            Some(got) if *got == want => {
                self.pos += 1;
                Ok(span)
            }
            Some(got) => Err(ScriptError::new(
                format!("expected {}, found {}", what, describe(got)),
                span,
            )),
            None => Err(ScriptError::new(
                format!("expected {}, found end of input", what),
                span,
            )),
        }
    }

    fn expr(&mut self) -> Result<Expr, ScriptError> {
        self.choice()
    }

    fn choice(&mut self) -> Result<Expr, ScriptError> {
        let mut branches = vec![self.sequence()?];
        while self.peek() == Some(&Tok::Pipe) {
            self.bump();
            branches.push(self.sequence()?);
        }
        Ok(if branches.len() == 1 {
            branches.pop().unwrap()
        } else {
            Expr::Choice(branches)
        })
    }

    fn sequence(&mut self) -> Result<Expr, ScriptError> {
        let mut steps = vec![self.primary()?];
        while self.peek() == Some(&Tok::Semi) {
            // A `;` before `}`-less end-of-definition is a terminator, not a
            // separator; only continue if something follows that can start an
            // expression.
            if !matches!(
                self.toks.get(self.pos + 1).map(|s| &s.tok),
                Some(Tok::Ident(_)) | Some(Tok::LParen)
            ) {
                break;
            }
            self.bump();
            steps.push(self.primary()?);
        }
        Ok(if steps.len() == 1 {
            steps.pop().unwrap()
        } else {
            Expr::Seq(steps)
        })
    }

    fn primary(&mut self) -> Result<Expr, ScriptError> {
        let span = self.span();
        match self.peek() {
            Some(Tok::LParen) => {
                self.bump();
                let inner = self.expr()?;
                self.expect(Tok::RParen, "')'")?;
                Ok(inner)
            }
            Some(Tok::Ident(_)) => {
                let Some(Spanned {
                    tok: Tok::Ident(name),
                    ..
                }) = self.bump()
                else {
                    unreachable!("peeked an identifier")
                };
                if self.peek() == Some(&Tok::LBrace) {
                    self.bump();
                    let term = self.term()?;
                    let close = self.expect(Tok::RBrace, "'}' or an instruction")?;
                    return Ok(Expr::Term(name.clone(), (span.0, close.1), term));
                }
                if self.peek() != Some(&Tok::LParen) {
                    return Ok(Expr::Name(name.clone(), span));
                }
                self.bump();
                let mut args = Vec::new();
                if self.peek() != Some(&Tok::RParen) {
                    loop {
                        args.push(self.arg()?);
                        if self.peek() == Some(&Tok::Comma) {
                            self.bump();
                            continue;
                        }
                        break;
                    }
                }
                let close = self.expect(Tok::RParen, "')' or ','")?;
                Ok(Expr::Call(name.clone(), (span.0, close.1), args))
            }
            Some(other) => Err(ScriptError::new(
                format!("expected a tactic, found {}", describe(other)),
                span,
            )),
            None => Err(ScriptError::new(
                "expected a tactic, found end of input",
                span,
            )),
        }
    }

    fn arg(&mut self) -> Result<Arg, ScriptError> {
        if let Some(Tok::Int(n)) = self.peek() {
            let n = *n;
            self.bump();
            return Ok(Arg::Int(n));
        }
        // `name: expr`. Two tokens of lookahead, since a bare name is a tactic
        // and only the colon says otherwise.
        if let Some(Tok::Ident(name)) = self.peek()
            && self.toks.get(self.pos + 1).map(|s| &s.tok) == Some(&Tok::Colon)
        {
            let name = name.clone();
            let span = self.span();
            self.bump();
            self.bump();
            return Ok(Arg::Named(name, span, self.expr()?));
        }
        Ok(Arg::Expr(self.expr()?))
    }

    /// A run of instructions, up to but not including the closing brace.
    ///
    /// Deliberately a small language: enough to name the code you want put
    /// into a term, and no more. It has no calls — a term is written here
    /// rather than compiled from a sentence, so there is nothing to name — and
    /// no branches, since a branch needs two blocks and a condition and would
    /// be a program rather than a term.
    fn term(&mut self) -> Result<Vec<Node>, ScriptError> {
        let mut out = Vec::new();
        while !matches!(self.peek(), Some(&Tok::RBrace) | None) {
            out.push(self.instruction()?);
        }
        Ok(out)
    }

    fn instruction(&mut self) -> Result<Node, ScriptError> {
        let span = self.span();
        let Some(Spanned {
            tok: Tok::Ident(word),
            ..
        }) = self.bump()
        else {
            return Err(ScriptError::new("expected an instruction", span)
                .with_help(format!("instructions: {}", INSTRUCTION_WORDS.join(", "))));
        };
        let word = word.clone();

        // The two nested forms. A branch reads as a program rather than a
        // value, which is why a term used to decline one — but a `Node::Branch`
        // carries no condition, only the two arms, and the condition it pops is
        // whatever the stack already holds. So it is a node like any other, and
        // excluding it left `annihilate` with no way to be read backwards at
        // `m = 0`: nothing could write the `branch { } { }` to introduce.
        if word == "branch" {
            let then_body = self.block()?;
            let else_body = self.block()?;
            return Ok(Node::Branch {
                then_origin: TERM_ORIGIN.to_string(),
                then_body,
                else_origin: TERM_ORIGIN.to_string(),
                else_body,
            });
        }

        // `dip k { ... }` is the one nested form, and the only way to write a
        // term that hides part of the stack from itself.
        if word == "dip" {
            let depth = self.count(&word, span)?;
            return Ok(Node::Dip {
                depth,
                origins: Vec::new(),
                body: self.block()?,
            });
        }

        if word == "push" {
            return Ok(Node::Op(Instruction::Push(self.literal(span)?)));
        }

        // The one thing in a term that reaches outside it. A term used to hold
        // no calls because there was nothing for one to name — the code was
        // written here rather than compiled from a sentence — but `share` is
        // about running *a function* twice, and the function has a name.
        if word == "jump" {
            return Ok(Node::Call {
                depth: 0,
                target: self.sentence(span)?,
            });
        }

        let inst = match word.as_str() {
            "pick" => Instruction::Pick(self.count(&word, span)?),
            "roll" => Instruction::Roll(self.count(&word, span)?),
            "tuple" => Instruction::Tuple(self.count(&word, span)?),
            "untuple" => Instruction::Untuple(self.count(&word, span)?),
            other => match plain_instruction(other) {
                Some(inst) => inst,
                None => {
                    return Err(ScriptError::new(
                        format!("'{}' is not an instruction a term may hold", other),
                        span,
                    )
                    .with_help(format!("instructions: {}", INSTRUCTION_WORDS.join(", "))));
                }
            },
        };
        Ok(Node::Op(inst))
    }

    /// The sentence a term names, resolved the way the command line resolves
    /// one: an index, an exact name, or an unambiguous trailing part of one.
    fn sentence(&mut self, span: Span) -> Result<bytecode::SentenceIndex, ScriptError> {
        let (ident, ident_span) = match self.peek() {
            Some(Tok::Ident(name)) => {
                let name = name.clone();
                let span = self.span();
                self.bump();
                (name, span)
            }
            Some(Tok::Int(n)) => {
                let name = n.to_string();
                let span = self.span();
                self.bump();
                (name, span)
            }
            _ => {
                return Err(ScriptError::new("`jump` needs a sentence", span)
                    .with_help("a name, a unique trailing part of one, or an index"));
            }
        };
        let Some(prog) = self.prog else {
            return Err(
                ScriptError::new("naming a sentence needs a program", ident_span).with_help(
                    "a term that names one cannot be compiled on its own, since \
                     the sentence's arity is what says how wide a window the \
                     rule reads",
                ),
            );
        };
        resolve_sentence(prog.library(), &ident).map_err(|why| ScriptError::new(why, ident_span))
    }

    /// A braced run of instructions: a dip body, or one arm of a branch.
    fn block(&mut self) -> Result<Vec<Node>, ScriptError> {
        self.expect(Tok::LBrace, "'{'")?;
        let body = self.term()?;
        self.expect(Tok::RBrace, "'}'")?;
        Ok(body)
    }

    fn count(&mut self, word: &str, span: Span) -> Result<usize, ScriptError> {
        match self.peek() {
            Some(Tok::Int(n)) => {
                let n = *n;
                self.bump();
                Ok(n)
            }
            _ => Err(ScriptError::new(format!("`{}` needs a number", word), span)
                .with_help(format!("for example `{} 0`", word))),
        }
    }

    fn literal(&mut self, span: Span) -> Result<Value, ScriptError> {
        match self.peek() {
            Some(Tok::Int(n)) => {
                let n = *n as i64;
                self.bump();
                Ok(Value::Int(n))
            }
            Some(Tok::Ident(word)) if word == "true" || word == "false" => {
                let yes = word == "true";
                self.bump();
                Ok(Value::Bool(yes))
            }
            // A const string is its text, so unlike a symbol it is built here
            // rather than looked up, and needs no program to be compiled
            // against.
            Some(Tok::Str(_)) => {
                let Some(Tok::Str(text)) = self.bump().map(|s| s.tok.clone()) else {
                    unreachable!("peeked a string literal")
                };
                Ok(Value::ConstString(text))
            }
            // Anything else that reads as a name is a symbol, looked up rather
            // than built: `Symbol` compares by `id`, so one made from its text
            // would equal nothing in the program.
            Some(Tok::Ident(_)) => {
                let ident_span = self.span();
                let Some(Tok::Ident(name)) = self.bump().map(|s| s.tok.clone()) else {
                    unreachable!("peeked an identifier")
                };
                let Some(prog) = self.prog else {
                    return Err(
                        ScriptError::new("naming a symbol needs a program", ident_span).with_help(
                            "a symbol is a declaration in the library, not a \
                             piece of syntax, so a term that pushes one cannot \
                             be compiled on its own",
                        ),
                    );
                };
                resolve_symbol(prog.library(), &name)
                    .map_err(|why| ScriptError::new(why, ident_span))
            }
            _ => Err(ScriptError::new("`push` needs a literal", span).with_help(
                "an integer, `true`/`false`, a `\"const string\"`, or a symbol \
                 by name. Floats have no syntax here yet",
            )),
        }
    }
}

/// The instructions a term may name that take no argument.
///
/// Shared with [`crate::serial`], which reads and writes the same vocabulary:
/// a second copy of this table would be a silent hazard rather than a
/// duplication, since a word that meant one instruction in a tactic and another
/// in a derivation file would be worse than one that meant nothing.
pub(crate) fn plain_instruction(word: &str) -> Option<Instruction> {
    Some(match word {
        "drop" => Instruction::Drop,
        "equal" => Instruction::Equal,
        "greater" => Instruction::Greater,
        "less" => Instruction::Less,
        "add" => Instruction::Add,
        "subtract" => Instruction::Subtract,
        "multiply" => Instruction::Multiply,
        "divide" => Instruction::Divide,
        "modulo" => Instruction::Modulo,
        "not" => Instruction::Not,
        "negate" => Instruction::Negate,
        "and" => Instruction::And,
        "or" => Instruction::Or,
        "is_int" => Instruction::IsInt,
        "is_bool" => Instruction::IsBool,
        "is_float" => Instruction::IsFloat,
        "is_const_string" => Instruction::IsConstString,
        "is_symbol" => Instruction::IsSymbol,
        "is_tuple" => Instruction::IsTuple,
        "tuple_length" => Instruction::TupleLength,
        "const_string_len" => Instruction::ConstStringLen,
        "const_string_char_at" => Instruction::ConstStringCharAt,
        _ => return None,
    })
}

/// The word that names an argument-free instruction, which is
/// [`plain_instruction`] the other way round.
///
/// It exists because a derivation is written down as well as read, and the two
/// directions have to be inverse or a file would not mean the run it records.
/// `plain_words_and_instructions_are_inverse` holds them to it rather than
/// leaving the pair to be maintained by eye.
pub(crate) fn plain_word(inst: &Instruction) -> Option<&'static str> {
    Some(match inst {
        Instruction::Drop => "drop",
        Instruction::Equal => "equal",
        Instruction::Greater => "greater",
        Instruction::Less => "less",
        Instruction::Add => "add",
        Instruction::Subtract => "subtract",
        Instruction::Multiply => "multiply",
        Instruction::Divide => "divide",
        Instruction::Modulo => "modulo",
        Instruction::Not => "not",
        Instruction::Negate => "negate",
        Instruction::And => "and",
        Instruction::Or => "or",
        Instruction::IsInt => "is_int",
        Instruction::IsBool => "is_bool",
        Instruction::IsFloat => "is_float",
        Instruction::IsConstString => "is_const_string",
        Instruction::IsSymbol => "is_symbol",
        Instruction::IsTuple => "is_tuple",
        Instruction::TupleLength => "tuple_length",
        Instruction::ConstStringLen => "const_string_len",
        Instruction::ConstStringCharAt => "const_string_char_at",
        _ => return None,
    })
}

/// The argument-free instructions, by name. The domain both functions above
/// are defined on, written once so the test can sweep it.
#[cfg(test)]
const PLAIN_WORDS: &[&str] = &[
    "drop",
    "equal",
    "greater",
    "less",
    "add",
    "subtract",
    "multiply",
    "divide",
    "modulo",
    "not",
    "negate",
    "and",
    "or",
    "is_int",
    "is_bool",
    "is_float",
    "is_const_string",
    "is_symbol",
    "is_tuple",
    "tuple_length",
    "const_string_len",
    "const_string_char_at",
];

/// Where a block written in a tactic came from, for the listing.
///
/// Phase 4 labels an inline block `<inline>`; this is the same courtesy for
/// code that was never compiled at all. Provenance is not part of a term's
/// identity — `same_effect` ignores it — so this only ever shows up in a
/// listing, saying that the code came from the tactic rather than a sentence.
pub(crate) const TERM_ORIGIN: &str = "<term>";

/// What a term may hold, for an error message.
///
/// `panic`, `assert` and `assert_eq` are absent on purpose: they are the three
/// instructions that can fail, and the whole tool is restricted to code that
/// cannot. Introducing one would break the precondition every equation is
/// stated under.
const INSTRUCTION_WORDS: &[&str] = &[
    "pick n",
    "branch { .. } { .. }",
    "roll n",
    "tuple n",
    "untuple n",
    "push <int|true|false|\"const string\"|symbol>",
    "dip n { .. }",
    "drop",
    "equal",
    "greater",
    "less",
    "add",
    "subtract",
    "multiply",
    "divide",
    "modulo",
    "not",
    "negate",
    "and",
    "or",
    "is_int",
    "is_bool",
    "is_float",
    "is_const_string",
    "is_symbol",
    "is_tuple",
    "tuple_length",
    "const_string_len",
    "const_string_char_at",
];

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Ident(name) => format!("'{}'", name),
        Tok::Int(n) => format!("'{}'", n),
        Tok::Str(text) => format!("string literal \"{}\"", text),
        Tok::Tactic => "'tactic'".to_string(),
        Tok::Strategy => "'strategy'".to_string(),
        Tok::Proof => "'proof'".to_string(),
        Tok::Eq => "'='".to_string(),
        Tok::Semi => "';'".to_string(),
        Tok::Comma => "','".to_string(),
        Tok::Colon => "':'".to_string(),
        Tok::Pipe => "'|'".to_string(),
        Tok::LBrace => "'{'".to_string(),
        Tok::RBrace => "'}'".to_string(),
        Tok::LParen => "'('".to_string(),
        Tok::RParen => "')'".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Definitions and resolution
// ---------------------------------------------------------------------------

/// A `.hant`: tactic definitions, plus a proof of each identity its sibling
/// `.hana` states.
pub(crate) struct ProofFile {
    /// Seeded from the prelude — and from any `--tactics` file — and then
    /// **file-local**. A tactic defined in one `.hant` is invisible to every
    /// other one, because a proof has to be readable beside the identity it
    /// proves, and a name that could have come from any of a dozen files is
    /// not. A corpus-wide prelude is `prove --tactics <file>`, which is the
    /// same mechanism said out loud.
    pub(crate) defs: Definitions,
    /// In source order, which is the order they are checked in.
    pub(crate) proofs: Vec<ProofDef>,
}

/// One `proof <identity> = <tactic>;`.
pub(crate) struct ProofDef {
    /// The identity as written. Resolved against the library, not here — a
    /// `.hant` is not part of the module tree, so it has no scope of its own
    /// and suffix matching is the only reading available.
    pub(crate) path: String,
    pub(crate) path_span: Span,
    /// The expression's span in the file, for an error that has to point at it.
    pub(crate) span: Span,
    body: Expr,
}

impl ProofFile {
    /// Parses a `.hant` against a program.
    ///
    /// Unlike `Definitions::load` this has the program in hand from the start,
    /// so a term here may name a sentence — `share { jump helper }` works in a
    /// proof and in a tactic defined beside it, where in a `--tactics` file it
    /// does not. That falls out of *when* the two are read: a `--tactics` file
    /// is loaded before a corpus is chosen, and a `.hant` only ever after one.
    ///
    /// It also means the whole file is parsed in one pass over its own tokens,
    /// so every span is an offset into the file rather than into a slice of it.
    /// Compiling each proof from its own substring would report line 1 of a
    /// one-line string for every error in every `.hant`.
    pub(crate) fn parse(
        source: &str,
        base: &Definitions,
        prog: &Program,
    ) -> Result<ProofFile, ScriptError> {
        let toks = tokenize(source)?;
        let mut p = Parser {
            toks: &toks,
            pos: 0,
            end: source.len(),
            prog: Some(prog),
        };
        let mut defs = base.clone();
        let mut proofs = Vec::new();
        defs.parse_defs(&mut p, Some(&mut proofs))?;
        Ok(ProofFile { defs, proofs })
    }

    /// Resolves one proof's expression against this file's definitions.
    ///
    /// A proof is a strategy, and a bare tactic is the strategy that runs it
    /// blind — see [`Definitions::resolve_proof`].
    pub(crate) fn compile(
        &self,
        proof: &ProofDef,
        prog: &Program,
    ) -> Result<Strategy, ScriptError> {
        self.defs.resolve_proof(&proof.body, Some(prog))
    }
}

/// A set of named tactics and strategies, built from the prelude plus any user
/// script.
#[derive(Clone)]
pub(crate) struct Definitions {
    defs: HashMap<String, Expr>,
    /// Declaration order, for `--list-tactics`.
    order: Vec<String>,
    /// Named strategies, in their own namespace.
    ///
    /// Empty until someone writes one: there is no strategy prelude, because a
    /// default route through a goal is the thing this layer deliberately does
    /// not have. See [`crate::prover`].
    strategies: HashMap<String, Expr>,
}

impl Definitions {
    pub(crate) fn new() -> Self {
        Definitions {
            defs: HashMap::new(),
            order: Vec::new(),
            strategies: HashMap::new(),
        }
    }

    /// Parses `tactic NAME = expr;` definitions, later ones shadowing earlier.
    pub(crate) fn load(&mut self, source: &str) -> Result<(), ScriptError> {
        let toks = tokenize(source)?;
        let mut p = Parser {
            toks: &toks,
            pos: 0,
            end: source.len(),
            // Definitions are parsed once, before any program is chosen, so a
            // *stored* term may not name a sentence. Only the expression given
            // on the command line can, which is where `compile_with` gets one.
            prog: None,
        };

        self.parse_defs(&mut p, None)
    }

    /// The definition loop, shared by `--tactics` files and `.hant` files.
    ///
    /// `proofs` is what tells the two apart. Given `None` a `proof` is refused
    /// by name rather than by a parse failure, so a `.hant` handed to
    /// `--tactics` says what is wrong with it. A `strategy` is allowed either
    /// way: it names a route through a goal without discharging one, which is
    /// as shareable across a corpus as a tactic is.
    fn parse_defs(
        &mut self,
        p: &mut Parser,
        mut proofs: Option<&mut Vec<ProofDef>>,
    ) -> Result<(), ScriptError> {
        while let Some(tok) = p.peek() {
            let kind = match tok {
                Tok::Tactic => Def::Tactic,
                Tok::Strategy => Def::Strategy,
                Tok::Proof => Def::Proof,
                _ => {
                    return Err(ScriptError::new(
                        "expected 'tactic', 'strategy' or 'proof'",
                        p.span(),
                    ));
                }
            };
            let keyword_span = p.span();
            p.bump();

            let name_span = p.span();
            let name = match p.bump() {
                Some(Spanned {
                    tok: Tok::Ident(name),
                    ..
                }) => name.clone(),
                _ => {
                    let what = match kind {
                        Def::Proof => "expected the name of an identity",
                        Def::Strategy => "expected a strategy name",
                        Def::Tactic => "expected a tactic name",
                    };
                    return Err(ScriptError::new(what, name_span));
                }
            };

            if kind == Def::Strategy {
                // Three namespaces now, and a name that lived in two of them
                // would make a proof unreadable: which layer `foo` belonged to
                // would decide whether it transformed a term or discharged a
                // goal.
                if STRATEGY_FORMS.contains(&name.as_str()) {
                    return Err(ScriptError::new(
                        format!("'{}' is a strategy form", name),
                        name_span,
                    )
                    .with_help("pick another name"));
                }
                if self.defs.contains_key(&name) || matcher_by_name(&name).is_some() {
                    return Err(ScriptError::new(
                        format!("'{}' is already a name", name),
                        name_span,
                    )
                    .with_help(
                        "rules, tactics and strategies are separate namespaces; \
                                 a name in two of them would not say which layer it \
                                 belongs to",
                    ));
                }
                p.expect(Tok::Eq, "'='")?;
                let body = p.expr()?;
                p.expect(Tok::Semi, "';'")?;
                self.strategies.insert(name, body);
                continue;
            }

            if kind == Def::Proof {
                let Some(proofs) = proofs.as_deref_mut() else {
                    return Err(ScriptError::new(
                        "`proof` is not a tactic definition",
                        keyword_span,
                    )
                    .with_help(
                        "a proof discharges an identity, so it belongs in the `.hant` \
                                 beside the `.hana` that states one; a `--tactics` file holds \
                                 `tactic NAME = expr;` and nothing else",
                    ));
                };
                p.expect(Tok::Eq, "'='")?;
                let body_start = p.span().0;
                let body = p.expr()?;
                let body_end = p.span().0;
                p.expect(Tok::Semi, "';'")?;

                // Two proofs of one identity is a mistake, where two tactics of
                // one name is shadowing. A tactic name is a binding, meant to
                // be overridable — that is what lets `--tactics` replace a
                // prelude entry. A proof is a claim discharged, and a claim
                // discharged twice was discharged once too often.
                if let Some(prior) = proofs.iter().find(|d| d.path == name) {
                    let (line, _) = prior.path_span;
                    return Err(ScriptError::new(
                        format!("'{}' is proved twice in this file", name),
                        name_span,
                    )
                    .with_help(format!(
                        "the first proof of it starts at byte {}; a tactic name shadows, \
                         but a proof does not",
                        line
                    )));
                }
                proofs.push(ProofDef {
                    path: name,
                    path_span: name_span,
                    span: (body_start, body_end.max(body_start)),
                    body,
                });
                continue;
            }

            if matcher_by_name(&name).is_some() {
                return Err(
                    ScriptError::new(format!("'{}' is a rule name", name), name_span).with_help(
                        "rules, tactics and strategies are separate namespaces; pick \
                         another name",
                    ),
                );
            }
            if self.strategies.contains_key(&name) {
                return Err(
                    ScriptError::new(format!("'{}' is a strategy name", name), name_span)
                        .with_help(
                            "a strategy discharges a goal and a tactic transforms a term; \
                             one name cannot mean both",
                        ),
                );
            }
            if name == "inv" {
                return Err(
                    ScriptError::new("'inv' is the backward-reading form", name_span)
                        .with_help("`inv(r)` names a rule, so it cannot also name a tactic"),
                );
            }
            p.expect(Tok::Eq, "'='")?;
            let body = p.expr()?;
            p.expect(Tok::Semi, "';'")?;

            if !self.defs.contains_key(&name) {
                self.order.push(name.clone());
            }
            self.defs.insert(name, body);
        }

        Ok(())
    }

    pub(crate) fn names(&self) -> &[String] {
        &self.order
    }

    // -----------------------------------------------------------------------
    // Strategies
    // -----------------------------------------------------------------------

    /// Resolves a proof body, which is a strategy.
    ///
    /// **A bare tactic keeps its meaning.** An expression that names no
    /// strategy is resolved as a tactic and wrapped in [`Strategy::Blind`],
    /// which is what a `.hant` written before this layer existed says and does.
    /// The coercion is the mirror of the error a *rule* gets in tactic position:
    /// there it is refused because `each(r)` and `once(r)` are both plausible,
    /// and here it is taken because there is only one thing a tactic can mean
    /// when it is handed a goal.
    /// Parses and resolves a proof body given as text, which is what `rewrite`
    /// has: a strategy off the command line rather than out of a `.hant`.
    ///
    /// The same shape as [`compile_with`](Definitions::compile_with) one layer
    /// up, and it exists so that `Expr` stays private to this module.
    pub(crate) fn compile_proof(
        &self,
        source: &str,
        prog: Option<&Program>,
    ) -> Result<Strategy, ScriptError> {
        let toks = tokenize(source)?;
        let mut p = Parser {
            toks: &toks,
            pos: 0,
            end: source.len(),
            prog,
        };
        let expr = p.expr()?;
        if let Some(tok) = p.peek() {
            return Err(ScriptError::new(
                format!("unexpected {} after the strategy", describe(tok)),
                p.span(),
            ));
        }
        self.resolve_proof(&expr, prog)
    }

    fn resolve_proof(&self, expr: &Expr, prog: Option<&Program>) -> Result<Strategy, ScriptError> {
        if self.mentions_strategy(expr) {
            self.resolve_strategy(expr, prog, &mut HashSet::new(), &mut HashSet::new())
        } else {
            Ok(Strategy::Blind(self.resolve(
                expr,
                prog,
                &mut HashSet::new(),
            )?))
        }
    }

    /// Whether this expression is written in the strategy language at all.
    ///
    /// Only the positions a strategy could legitimately occupy are looked at —
    /// the top level, and through `|` and `;`. The arguments of `each` are
    /// rules and the arguments of `repeat` are tactics, so a strategy form
    /// appearing inside one is a mistake to be reported by the tactic
    /// resolver in its own words, not a signal about the whole expression.
    fn mentions_strategy(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Name(name, _) => {
                BARE_MOVES.contains(&name.as_str()) || self.strategies.contains_key(name)
            }
            Expr::Call(name, _, _) => {
                STRATEGY_FORMS.contains(&name.as_str()) || self.strategies.contains_key(name)
            }
            Expr::Seq(parts) | Expr::Choice(parts) => {
                parts.iter().any(|e| self.mentions_strategy(e))
            }
            Expr::Term(_, _, _) => false,
        }
    }

    fn resolve_strategy(
        &self,
        expr: &Expr,
        prog: Option<&Program>,
        visiting: &mut HashSet<String>,
        tactics: &mut HashSet<String>,
    ) -> Result<Strategy, ScriptError> {
        match expr {
            Expr::Choice(parts) => Ok(Strategy::Choice(
                parts
                    .iter()
                    .map(|e| self.resolve_strategy(e, prog, visiting, tactics))
                    .collect::<Result<_, _>>()?,
            )),

            // `;` between moves, where each rewrites one side of the goal and
            // hands the rest of the sequence what it left. This is the reading
            // that makes `cleanup ; rhs(dips)` mean what it looks like.
            //
            // A strategy that *forks* — `descend`, or a choice — discharges the
            // goal rather than narrowing it, so it can only come last, and there
            // is nothing arbitrary about that: a branch has two sub-goals and a
            // sequence has one place to put the next thing.
            Expr::Seq(parts) => {
                let (last, init) = parts.split_last().expect("a sequence has parts");
                let mut moves: Vec<Move> = init
                    .iter()
                    .map(|e| self.resolve_move(e, prog, tactics))
                    .collect::<Result<_, _>>()?;
                if self.is_move(last) {
                    moves.push(self.resolve_move(last, prog, tactics)?);
                    return Ok(Strategy::Sequence { moves, then: None });
                }
                Ok(Strategy::Sequence {
                    moves,
                    then: Some(Box::new(
                        self.resolve_strategy(last, prog, visiting, tactics)?,
                    )),
                })
            }

            Expr::Name(name, span) if self.strategies.contains_key(name) => {
                let body = &self.strategies[name];
                if !visiting.insert(name.to_string()) {
                    return Err(ScriptError::new(
                        format!("strategy '{}' is defined in terms of itself", name),
                        *span,
                    )
                    .with_help(
                        "strategy definitions may not recurse, for the reason tactic \
                         definitions may not: there is no measure that says a goal is \
                         getting smaller. Write the depth you mean",
                    ));
                }
                let out = self.resolve_strategy(body, prog, visiting, tactics);
                visiting.remove(name);
                out
            }

            Expr::Call(name, span, args) if self.strategies.contains_key(name) => Err(
                ScriptError::new(format!("strategy '{}' takes no arguments", name), *span)
                    .with_help("only the strategy forms take arguments; write it bare"),
            ),

            Expr::Call(name, span, args) if STRATEGY_FORMS.contains(&name.as_str()) => {
                self.strategy_form(name, *span, args, prog, visiting, tactics)
            }

            // A move on its own is a sequence of one.
            Expr::Name(name, _) if BARE_MOVES.contains(&name.as_str()) => Ok(Strategy::Sequence {
                moves: vec![self.resolve_move(expr, prog, tactics)?],
                then: None,
            }),

            // Everything else is a tactic, which means today's reading.
            other => Ok(Strategy::Blind(self.resolve(other, prog, tactics)?)),
        }
    }

    /// One element of a `;` sequence.
    ///
    /// Only the forms that rewrite a side can appear here. `peel` and `descend`
    /// take the rest of the proof as an argument — they cut the goal up and hand
    /// the pieces on — so they are not something a later move could follow, and
    /// saying that is better than letting one be written and quietly ignored.
    fn resolve_move(
        &self,
        expr: &Expr,
        prog: Option<&Program>,
        tactics: &mut HashSet<String>,
    ) -> Result<Move, ScriptError> {
        if let Expr::Name(name, _) = expr {
            match name.as_str() {
                "peel" => return Ok(Move::Peel),
                "inline" => return Ok(Move::Inline),
                _ => {}
            }
        }
        if let Expr::Call(name, span, args) = expr
            && MOVES.contains(&name.as_str())
        {
            let [Arg::Expr(inner)] = args.as_slice() else {
                return Err(ScriptError::new(
                    format!("`{}` takes exactly one tactic", name),
                    *span,
                )
                .with_help(format!("for example `{}(cleanup)`", name)));
            };
            let tactic = self.resolve(inner, prog, &mut HashSet::new())?;
            return Ok(match name.as_str() {
                "exact" => Move::Left(tactic),
                "normalize" => Move::Both(tactic),
                _ => Move::Right(tactic),
            });
        }
        if let Expr::Call(name, span, _) = expr
            && STRATEGY_FORMS.contains(&name.as_str())
        {
            return Err(
                ScriptError::new(format!("`{}` has to come last", name), *span).with_help(
                    "it forks the goal into more than one, and a sequence has one \
                     place to put what follows. Put the rest inside it instead",
                ),
            );
        }
        // Anything else is a tactic, and a tactic drives the left-hand side.
        Ok(Move::Left(self.resolve(expr, prog, tactics)?))
    }

    /// Whether this can be one of a sequence rather than the end of it.
    ///
    /// Everything is, except the two kinds of thing that discharge a goal rather
    /// than narrowing it: a form that forks, and a named strategy — which is
    /// arbitrary, so nothing here can say what it leaves behind. A plain tactic
    /// is a move like any other, since driving the left-hand side is what one
    /// does to a goal.
    fn is_move(&self, expr: &Expr) -> bool {
        let named_strategy = |name: &String| self.strategies.contains_key(name);
        match expr {
            Expr::Name(name, _) => BARE_MOVES.contains(&name.as_str()) || !named_strategy(name),
            Expr::Call(name, _, _) => {
                MOVES.contains(&name.as_str())
                    || !(STRATEGY_FORMS.contains(&name.as_str()) || named_strategy(name))
            }
            // A rule completed by a term, which is a tactic, which drives the
            // left. (It will be refused for other reasons, in its own words.)
            Expr::Term(_, _, _) => true,
            Expr::Seq(_) | Expr::Choice(_) => false,
        }
    }

    fn strategy_form(
        &self,
        name: &str,
        span: Span,
        args: &[Arg],
        prog: Option<&Program>,
        visiting: &mut HashSet<String>,
        tactics: &mut HashSet<String>,
    ) -> Result<Strategy, ScriptError> {
        // The two that take a tactic and run it, and the two that take a
        // strategy and cut the goal up first.
        let one_tactic = |what: &str| -> Result<Tactic, ScriptError> {
            let [Arg::Expr(inner)] = args else {
                return Err(
                    ScriptError::new(format!("`{}` takes exactly one tactic", name), span)
                        .with_help(format!("for example `{}(cleanup)`", what)),
                );
            };
            self.resolve(inner, prog, &mut HashSet::new())
        };

        match name {
            "exact" | "normalize" | "rhs" => Ok(Strategy::Sequence {
                moves: vec![match name {
                    "exact" => Move::Left(one_tactic(name)?),
                    "normalize" => Move::Both(one_tactic(name)?),
                    _ => Move::Right(one_tactic(name)?),
                }],
                then: None,
            }),
            "peel" | "inline" => Err(ScriptError::new(
                format!("`{}` takes no arguments", name),
                span,
            )
            .with_help(format!(
                "it narrows the goal and leaves one, so it is a move rather \
                             than something taking the rest of the proof: write \
                             `{} ; <the rest>`",
                name
            ))),
            _ => self.descend(span, args, prog, visiting, tactics),
        }
    }

    /// `descend(body: s)`, or `descend(then: s, else: s)`.
    ///
    /// Named parts rather than an order, because a branch has two children and
    /// both have to be discharged — and because which arm a strategy was meant
    /// for is exactly the thing a reader of a proof needs to see.
    fn descend(
        &self,
        span: Span,
        args: &[Arg],
        prog: Option<&Program>,
        visiting: &mut HashSet<String>,
        tactics: &mut HashSet<String>,
    ) -> Result<Strategy, ScriptError> {
        let (mut body, mut then, mut els) = (None, None, None);
        for arg in args {
            let Arg::Named(part, part_span, inner) = arg else {
                return Err(
                    ScriptError::new("`descend` takes named parts", span).with_help(
                        "`descend(body: t)` reaches into a frame, and \
                         `descend(then: t, else: t)` into the arms of a branch",
                    ),
                );
            };
            let slot = match part.as_str() {
                "body" => &mut body,
                "then" => &mut then,
                "else" => &mut els,
                other => {
                    return Err(ScriptError::new(
                        format!("'{}' is not a part a node has", other),
                        *part_span,
                    )
                    .with_help("the parts are `body`, `then` and `else`"));
                }
            };
            if slot.is_some() {
                return Err(ScriptError::new(
                    format!("`{}` is given twice", part),
                    *part_span,
                ));
            }
            *slot = Some(Box::new(
                self.resolve_strategy(inner, prog, visiting, tactics)?,
            ));
        }

        match (body, then, els) {
            (None, None, None) => Err(ScriptError::new(
                "`descend` needs a part to descend into",
                span,
            )
            .with_help("`descend(body: t)` for a frame, `descend(then: t, else: t)` for a branch")),
            (Some(body), None, None) => Ok(Strategy::Descend(Descent::Body(body))),
            (Some(_), _, _) => Err(ScriptError::new(
                "`descend` mixes a body with branch arms",
                span,
            )
            .with_help("a frame has a body and a branch has two arms; no node has both")),
            (None, then, els) => Ok(Strategy::Descend(Descent::Arms { then, els })),
        }
    }

    /// Parses and resolves a single expression against these definitions.
    ///
    /// No program, so a term may not name a sentence. Every other tactic
    /// compiles, which is what keeps the prelude checkable on its own.
    #[cfg(test)]
    pub(crate) fn compile(&self, source: &str) -> Result<Tactic, ScriptError> {
        self.compile_with(source, None)
    }

    /// The same, with a program in hand, so a term may name a sentence.
    ///
    /// Everything else about a tactic is still settled here rather than at run
    /// time — the rule names, the shapes of the combinators, and the arity of
    /// every term. What the program adds is the one fact a term cannot supply
    /// for itself: what `jump foo` does to the stack, which is how wide a
    /// window the rule holding it reads.
    pub(crate) fn compile_with(
        &self,
        source: &str,
        prog: Option<&Program>,
    ) -> Result<Tactic, ScriptError> {
        let toks = tokenize(source)?;
        let mut p = Parser {
            toks: &toks,
            pos: 0,
            end: source.len(),
            prog,
        };
        let expr = p.expr()?;
        if let Some(tok) = p.peek() {
            return Err(ScriptError::new(
                format!("unexpected {} after the tactic", describe(tok)),
                p.span(),
            ));
        }
        self.resolve(&expr, prog, &mut HashSet::new())
    }

    fn resolve(
        &self,
        expr: &Expr,
        prog: Option<&Program>,
        visiting: &mut HashSet<String>,
    ) -> Result<Tactic, ScriptError> {
        match expr {
            Expr::Seq(parts) => Ok(Tactic::Seq(
                parts
                    .iter()
                    .map(|e| self.resolve(e, prog, visiting))
                    .collect::<Result<_, _>>()?,
            )),
            Expr::Choice(parts) => Ok(Tactic::Choice(
                parts
                    .iter()
                    .map(|e| self.resolve(e, prog, visiting))
                    .collect::<Result<_, _>>()?,
            )),
            Expr::Name(name, span) => self.resolve_name(name, *span, prog, visiting),
            Expr::Call(name, span, args) => self.resolve_call(name, *span, args, prog, visiting),
            // A matcher with a term is not a tactic on its own: it still has
            // to be placed. Saying so here is the same courtesy `each`/`once`
            // extend to a bare rule name.
            Expr::Term(name, span, _) => Err(ScriptError::new(
                format!("'{}' is a rule, not a tactic", name),
                *span,
            )
            .with_help(format!(
                "a rule has to be placed somewhere: write `once({} {{ ... }})` \
                 for the first match, or `each(...)` for every one",
                name
            ))),
        }
    }

    fn resolve_name(
        &self,
        name: &str,
        span: Span,
        prog: Option<&Program>,
        visiting: &mut HashSet<String>,
    ) -> Result<Tactic, ScriptError> {
        match name {
            "id" => return Ok(Tactic::Id),
            "fail" => return Ok(Tactic::Fail),
            _ => {}
        }

        if matcher_by_name(name).is_some() {
            return Err(
                ScriptError::new(format!("'{}' is a rule, not a tactic", name), span).with_help(
                    format!(
                        "a rule has to be placed somewhere: write `each({})` to apply it \
                 everywhere in a sequence, or `once({})` for the first match",
                        name, name
                    ),
                ),
            );
        }

        if COMBINATORS.iter().any(|(n, _)| *n == name) {
            return Err(
                ScriptError::new(format!("'{}' needs arguments", name), span)
                    .with_help(format!("write `{}(...)`", name)),
            );
        }

        let Some(body) = self.defs.get(name) else {
            return Err(
                ScriptError::new(format!("unknown tactic '{}'", name), span).with_help(format!(
                    "known tactics: {}; combinators: {}",
                    self.order.join(", "),
                    COMBINATORS
                        .iter()
                        .map(|(n, _)| *n)
                        .collect::<Vec<_>>()
                        .join(", ")
                )),
            );
        };

        if !visiting.insert(name.to_string()) {
            return Err(ScriptError::new(
                format!("tactic '{}' is defined in terms of itself", name),
                span,
            )
            .with_help(
                "tactic definitions may not recurse, so that `repeat` is the only \
                         unbounded construct in the language",
            ));
        }
        let out = self.resolve(body, prog, visiting);
        visiting.remove(name);
        out
    }

    fn resolve_call(
        &self,
        name: &str,
        span: Span,
        args: &[Arg],
        prog: Option<&Program>,
        visiting: &mut HashSet<String>,
    ) -> Result<Tactic, ScriptError> {
        // `inv(r)` is a rule, and a rule has to be placed — the same courtesy
        // a bare rule name gets, since `inv` looks exactly like a combinator.
        if name == "inv" {
            return Err(
                ScriptError::new("`inv(...)` is a rule, not a tactic", span).with_help(
                    "a rule has to be placed somewhere: write `each(inv(fuse))` \
                     to apply it everywhere in a sequence, or `once(inv(fuse))` \
                     for the first match",
                ),
            );
        }

        let Some((_, shape)) = COMBINATORS.iter().find(|(n, _)| *n == name) else {
            if self.defs.contains_key(name) {
                return Err(ScriptError::new(
                    format!("tactic '{}' takes no arguments", name),
                    span,
                )
                .with_help("only combinators take arguments; write it bare"));
            }
            return Err(
                ScriptError::new(format!("unknown combinator '{}'", name), span).with_help(
                    format!(
                        "combinators: {}",
                        COMBINATORS
                            .iter()
                            .map(|(n, _)| *n)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ),
            );
        };

        match shape {
            Shape::CountAndRules => {
                let [Arg::Int(n), rest @ ..] = args else {
                    return Err(ScriptError::new(
                        format!("`{}` takes a position and then rules", name),
                        span,
                    )
                    .with_help(format!("for example `{}(2, sink)`", name)));
                };
                let rules = self.rules(name, span, rest, prog)?;
                Ok(Tactic::At(*n, rules))
            }
            Shape::Descend => {
                let (index, inner) = match args {
                    [Arg::Expr(inner)] => (None, inner),
                    [Arg::Int(k), Arg::Expr(inner)] => (Some(*k), inner),
                    _ => {
                        return Err(ScriptError::new(
                            format!("`{}` takes a tactic, or an index and a tactic", name),
                            span,
                        )
                        .with_help(format!(
                            "`{}(t)` reaches every one; `{}(2, t)` reaches the one \
                             belonging to the node at 2",
                            name, name
                        )));
                    }
                };
                let sel = match name {
                    "then" => Selector::Then,
                    "else" => Selector::Else,
                    _ => Selector::Body,
                };
                let inner = Box::new(self.resolve(inner, prog, visiting)?);
                Ok(match index {
                    Some(k) => Tactic::IntoNth(k, sel, inner),
                    None => Tactic::Into(sel, inner),
                })
            }
            Shape::Rules => {
                if args.is_empty() {
                    return Err(ScriptError::new(
                        format!("`{}` needs at least one rule", name),
                        span,
                    ));
                }
                let rules = self.rules(name, span, args, prog)?;
                Ok(match name {
                    "each" => Tactic::Each(rules),
                    _ => Tactic::Once(rules),
                })
            }
            Shape::One => {
                let [Arg::Expr(inner)] = args else {
                    return Err(ScriptError::new(
                        format!("`{}` takes exactly one tactic", name),
                        span,
                    ));
                };
                let inner = Box::new(self.resolve(inner, prog, visiting)?);
                Ok(match name {
                    "try" => Tactic::Try(inner),
                    "must" => Tactic::Must(inner),
                    "repeat" => Tactic::Repeat(inner),
                    "children" => Tactic::Children(inner),
                    "bu" => Tactic::Bu(inner),
                    _ => Tactic::Td(inner),
                })
            }
            Shape::CountAndOne => {
                let [Arg::Int(n), Arg::Expr(inner)] = args else {
                    return Err(ScriptError::new(
                        format!("`{}` takes a count and a tactic", name),
                        span,
                    )
                    .with_help(format!("for example `{}(2, each(sink))`", name)));
                };
                Ok(Tactic::RepeatN(
                    *n,
                    Box::new(self.resolve(inner, prog, visiting)?),
                ))
            }
        }
    }

    /// The rule list `each`, `once` and `at` all take.
    fn rules(
        &self,
        name: &str,
        span: Span,
        args: &[Arg],
        prog: Option<&Program>,
    ) -> Result<Vec<Box<dyn Matcher>>, ScriptError> {
        if args.is_empty() {
            return Err(ScriptError::new(
                format!("`{}` needs at least one rule", name),
                span,
            ));
        }
        let mut rules: Vec<Box<dyn Matcher>> = Vec::new();
        for arg in args {
            let Arg::Expr(expr) = arg else {
                return Err(ScriptError::new(
                    format!("`{}` takes rule names, not tactics", name),
                    span,
                )
                .with_help(known_rules()));
            };
            rules.push(rule(name, span, expr, prog)?);
        }
        Ok(rules)
    }
}

/// One rule, in any of the three forms a rule list accepts.
///
/// A bare name, a name completed by a term, or `inv(r)` — the same equation
/// read the other way. `inv` is a form here rather than a combinator because
/// what it produces is a rule: it has still to be placed.
fn rule(
    placed_in: &str,
    span: Span,
    expr: &Expr,
    prog: Option<&Program>,
) -> Result<Box<dyn Matcher>, ScriptError> {
    match expr {
        Expr::Name(rule_name, rule_span) => {
            if term_matcher_names().contains(&rule_name.as_str()) {
                return Err(
                    ScriptError::new(format!("`{}` needs a term", rule_name), *rule_span)
                        .with_help(format!(
                            "say what to introduce: `{} {{ pick 0 }}`",
                            rule_name
                        )),
                );
            }
            matcher_by_name(rule_name).ok_or_else(|| {
                ScriptError::new(format!("unknown rule '{}'", rule_name), *rule_span)
                    .with_help(known_rules())
            })
        }

        Expr::Term(rule_name, rule_span, term) => {
            let Some(built) = matcher_with_term(rule_name, term.clone(), prog) else {
                let help = if matcher_by_name(rule_name).is_some() {
                    format!("`{}` takes no term; write it bare", rule_name)
                } else {
                    known_rules()
                };
                return Err(ScriptError::new(
                    format!("'{}' does not take a term", rule_name),
                    *rule_span,
                )
                .with_help(help));
            };
            built.map_err(|why| {
                ScriptError::new(
                    format!("`{}` cannot use that term: {}", rule_name, why),
                    *rule_span,
                )
            })
        }

        // `inv(r)`: whatever `r` places, read backwards. Nested and repeated
        // freely, so `inv(inv(sink))` is `sink` — which is worth allowing
        // rather than special-casing, since a definition may already say `inv`.
        Expr::Call(name, call_span, args) if name == "inv" => {
            let [Arg::Expr(inner)] = &args[..] else {
                return Err(ScriptError::new("`inv` takes exactly one rule", *call_span)
                    .with_help("for example `inv(fuse)`"));
            };
            let forward = rule(placed_in, span, inner, prog)?;
            forward.inverse().map_err(|why| {
                ScriptError::new(
                    format!("`{}` has no backward reading", forward.name()),
                    *call_span,
                )
                .with_help(why)
            })
        }

        // `counit(0)`: a rule narrowed by a number, the way `at(n, r)` is. It
        // is the *backward* reading this exists for — an equation whose other
        // side is empty has no window to read the number off.
        Expr::Call(name, call_span, args) if count_matcher_names().contains(&name.as_str()) => {
            let [Arg::Int(count)] = &args[..] else {
                return Err(
                    ScriptError::new(format!("`{}` takes one number", name), *call_span)
                        .with_help(format!("for example `{}(0)`", name)),
                );
            };
            matcher_with_count(name, *count)
                .ok_or_else(|| ScriptError::new(format!("`{}` takes no number", name), *call_span))
        }

        Expr::Call(name, call_span, _) => Err(ScriptError::new(
            format!("unknown rule form '{}(...)'", name),
            *call_span,
        )
        .with_help(format!(
            "`inv(r)` reads r's equation backwards, and {} take a number. {}",
            count_matcher_names().join(", "),
            known_rules()
        ))),

        Expr::Seq(_) | Expr::Choice(_) => Err(ScriptError::new(
            format!("`{}` takes rule names, not tactics", placed_in),
            span,
        )
        .with_help(known_rules())),
    }
}

/// The rule vocabulary, for an error message.
fn known_rules() -> String {
    let mut all = matcher_names();
    all.extend(term_matcher_names());
    all.sort();
    format!("rules: {}", all.join(", "))
}

enum Shape {
    /// Takes a position, then a comma-separated list of rule names.
    CountAndRules,
    /// Descends one level: a tactic, or an index and a tactic.
    ///
    /// Without the index it reaches every child of that kind; with it, one.
    /// The two readings are the difference between "every then arm" and "the
    /// then arm of the branch I mean".
    Descend,
    /// Takes a comma-separated list of rule names.
    ///
    /// Deliberately not a tactic expression: "the arguments to `each` are
    /// rules" is then a parse-time check with a real error message, rather
    /// than a runtime inspection of whether an argument happens to be a
    /// choice-of-rules.
    Rules,
    One,
    CountAndOne,
}

/// Which of the three things a definition defines.
#[derive(PartialEq, Eq, Clone, Copy)]
enum Def {
    Tactic,
    Strategy,
    Proof,
}

/// The strategy vocabulary.
///
/// Deliberately no `auto`, and deliberately no overlap with [`COMBINATORS`]:
/// `then(t)` is a tactic that reaches into every then arm, and it would be a
/// trap for the goal-directed descent to answer to the same word. `descend`
/// takes the arm by name instead.
const STRATEGY_FORMS: &[&str] = &["exact", "normalize", "rhs", "peel", "descend", "inline"];

/// The forms that rewrite one side and leave a goal, so may be sequenced.
const MOVES: &[&str] = &["exact", "normalize", "rhs"];

/// The moves that take no argument, since what they do to a goal is not
/// parameterized by a tactic.
const BARE_MOVES: &[&str] = &["peel", "inline"];

const COMBINATORS: &[(&str, Shape)] = &[
    ("each", Shape::Rules),
    ("once", Shape::Rules),
    // `once` told where to look instead of asked to find out.
    ("at", Shape::CountAndRules),
    ("try", Shape::One),
    // The counterpart to `try`: `must(t)` fails when `t` changes nothing,
    // which is how an aimed step says it missed.
    ("must", Shape::One),
    ("repeat", Shape::One),
    ("children", Shape::One),
    // `children` narrowed to one kind of child, and optionally to one node.
    ("then", Shape::Descend),
    ("else", Shape::Descend),
    ("body", Shape::Descend),
    ("bu", Shape::One),
    ("td", Shape::One),
    ("repeat_n", Shape::CountAndOne),
];

#[cfg(test)]
mod tests {
    use super::*;

    fn defs() -> Definitions {
        let mut d = Definitions::new();
        d.load(PRELUDE)
            .unwrap_or_else(|e| panic!("{}", e.render(PRELUDE)));
        d
    }

    fn err(src: &str) -> String {
        let e = defs()
            .compile(src)
            .err()
            .unwrap_or_else(|| panic!("`{}` unexpectedly compiled", src));
        format!(
            "{}{}",
            e.message,
            e.help.map(|h| format!(" | {}", h)).unwrap_or_default()
        )
    }

    /// Every word names an instruction, every instruction is named by the word
    /// it was found under, and nothing in the list is missing from either
    /// table. A derivation is written with one and read with the other.
    #[test]
    fn plain_words_and_instructions_are_inverse() {
        for word in PLAIN_WORDS {
            let inst = plain_instruction(word)
                .unwrap_or_else(|| panic!("'{}' is listed but names no instruction", word));
            assert_eq!(plain_word(&inst), Some(*word));
        }
        // ...and the list is the whole domain: a word a term accepts but the
        // list omits would be readable and unwritable.
        for word in INSTRUCTION_WORDS {
            let head = word.split(' ').next().unwrap_or(word);
            if plain_instruction(head).is_some() {
                assert!(
                    PLAIN_WORDS.contains(&head),
                    "'{}' is an instruction a term accepts but the list omits",
                    head
                );
            }
        }
    }

    #[test]
    fn the_prelude_compiles() {
        for name in defs().names() {
            defs()
                .compile(name)
                .unwrap_or_else(|e| panic!("{}", e.render(name)));
        }
    }

    #[test]
    fn a_rule_in_tactic_position_says_where_to_put_it() {
        let msg = err("repeat(bu(sink))");
        assert!(msg.contains("'sink' is a rule, not a tactic"), "{}", msg);
        assert!(msg.contains("each(sink)"), "{}", msg);
    }

    #[test]
    fn an_unknown_rule_lists_the_real_ones() {
        let msg = err("each(sinkk)");
        assert!(msg.contains("unknown rule 'sinkk'"), "{}", msg);
        assert!(msg.contains("sink"), "{}", msg);
    }

    #[test]
    fn a_tactic_is_not_accepted_where_a_rule_belongs() {
        // `each` takes rule names, so this is caught at compile time rather
        // than by inspecting the argument at run time.
        let msg = err("each(dips)");
        assert!(msg.contains("unknown rule 'dips'"), "{}", msg);
    }

    #[test]
    fn spans_point_at_the_offending_word() {
        let src = "repeat(bu(each(sink, nope)))";
        let e = defs().compile(src).unwrap_err();
        assert_eq!(&src[e.span.0..e.span.1], "nope");
    }

    #[test]
    fn recursive_definitions_are_rejected() {
        let mut d = defs();
        d.load("tactic loop = repeat(loop);").unwrap();
        let msg = d.compile("loop").unwrap_err();
        assert!(
            msg.message.contains("defined in terms of itself"),
            "{}",
            msg.message
        );
    }

    #[test]
    fn mutual_recursion_is_rejected_too() {
        let mut d = defs();
        d.load("tactic a = b; tactic b = a;").unwrap();
        assert!(
            d.compile("a")
                .unwrap_err()
                .message
                .contains("defined in terms of itself")
        );
    }

    #[test]
    fn a_tactic_may_not_shadow_a_rule_name() {
        let mut d = defs();
        let msg = d.load("tactic sink = id;").unwrap_err();
        assert!(msg.message.contains("is a rule name"), "{}", msg.message);
    }

    #[test]
    fn user_definitions_can_build_on_the_prelude() {
        let mut d = defs();
        d.load("tactic mine = dips; factoring;").unwrap();
        assert!(d.compile("mine").is_ok());
    }

    #[test]
    fn later_definitions_shadow_earlier_ones() {
        let mut d = defs();
        d.load("tactic mine = id;").unwrap();
        d.load("tactic mine = fail;").unwrap();
        // One entry in the listing, not two.
        assert_eq!(d.names().iter().filter(|n| *n == "mine").count(), 1);
    }

    #[test]
    fn trailing_junk_is_reported() {
        assert!(err("id id").contains("unexpected"));
    }

    #[test]
    fn combinator_arity_is_checked() {
        assert!(err("repeat_n(each(sink))").contains("count and a tactic"));
        assert!(err("try(each(sink), each(fuse))").contains("exactly one tactic"));
        assert!(err("each()").contains("at least one rule"));
    }

    #[test]
    fn sequences_and_choices_parse_at_the_right_precedence() {
        // `a; b | c` is `(a; b) | c`: `;` binds tighter than `|`.
        let d = defs();
        assert!(d.compile("id; id | fail").is_ok());
        assert!(d.compile("(id; id) | fail").is_ok());
        assert!(d.compile("id; (id | fail)").is_ok());
    }

    #[test]
    fn comments_and_newlines_are_skipped() {
        let mut d = defs();
        d.load("// leading comment\ntactic spaced =\n  id; // trailing\n  id;\n")
            .unwrap();
        assert!(d.compile("spaced").is_ok());
    }

    // -- terms --------------------------------------------------------------

    fn compiles(src: &str) -> bool {
        defs().compile(src).is_ok()
    }

    #[test]
    fn a_term_names_the_code_to_introduce() {
        assert!(compiles("each(introduce { pick 0 })"));
        assert!(compiles("once(introduce { pick 0 is_bool })"));
        assert!(compiles("once(introduce { dip 1 { pick 0 } })"));
        // A `push` has to be paired with something that consumes, or the term
        // takes no inputs and there is no drop for it to stand in front of.
        assert!(compiles("once(introduce { push 7 equal })"));
        assert!(compiles("once(introduce { push true and })"));
        // Mixed with ordinary rules in one placement.
        assert!(compiles("each(sink, introduce { pick 0 }, fuse)"));
    }

    #[test]
    fn a_term_may_hold_a_branch() {
        // It could not before, on the grounds that a branch needs a condition
        // and so reads as a program — but the node carries only the two arms,
        // and the condition it pops is whatever the stack already holds.
        assert!(compiles("once(introduce { branch { } { } })"));
        assert!(compiles("once(introduce { branch { not } { is_bool } })"));
        assert!(compiles("once(introduce { dip 1 { branch { } { } } })"));
        assert!(compiles(
            "once(introduce { branch { branch { } { } } { drop } })"
        ));
    }

    #[test]
    fn a_branch_in_a_term_is_held_to_what_the_arity_checker_asks() {
        // Arms that leave different amounts are not a program the compiler
        // would have accepted, and a term is code about to be spliced into
        // one. Nothing downstream would catch it, since a node's arity is read
        // off whichever arm answers first.
        let e = err("once(introduce { branch { drop } { } })");
        assert!(e.contains("leave different amounts"), "{}", e);
        assert!(e.contains("-1 against 0"), "{}", e);

        // Including one nested inside another block.
        let e = err("once(introduce { dip 1 { branch { drop } { } } })");
        assert!(e.contains("leave different amounts"), "{}", e);
    }

    #[test]
    fn the_instruction_list_mentions_a_branch() {
        let e = err("once(introduce { frobnicate })");
        assert!(e.contains("branch { .. } { .. }"), "{}", e);
    }

    #[test]
    fn a_rule_that_needs_a_term_says_so_when_written_bare() {
        let e = err("each(introduce)");
        assert!(e.contains("needs a term"), "{}", e);
        assert!(e.contains("pick 0"), "{}", e);
    }

    #[test]
    fn a_rule_that_takes_no_term_says_so_when_given_one() {
        let e = err("each(sink { pick 0 })");
        assert!(e.contains("does not take a term"), "{}", e);
        assert!(e.contains("bare"), "{}", e);
    }

    #[test]
    fn a_term_that_cannot_be_used_says_why() {
        // `panic` has no arity, so there is no saying what it discards.
        let e = err("each(introduce { panic })");
        assert!(e.contains("not an instruction"), "{}", e);
        // And one that consumes nothing is refused with its own reason.
        let e = err("each(introduce { push 1 })");
        assert!(e.contains("cannot use that term"), "{}", e);
    }

    #[test]
    fn an_unknown_instruction_points_at_the_ones_that_exist() {
        let e = err("each(introduce { frobnicate })");
        assert!(e.contains("frobnicate"), "{}", e);
        assert!(e.contains("pick n"), "{}", e);
    }

    #[test]
    fn an_instruction_missing_its_number_says_so() {
        let e = err("each(introduce { pick })");
        assert!(e.contains("needs a number"), "{}", e);
        let e = err("each(introduce { push })");
        assert!(e.contains("needs a literal"), "{}", e);
    }

    #[test]
    fn a_term_matcher_still_has_to_be_placed() {
        let e = err("introduce { pick 0 }");
        assert!(e.contains("not a tactic"), "{}", e);
        assert!(e.contains("once("), "{}", e);
    }

    #[test]
    fn an_unclosed_term_is_an_error_rather_than_a_silent_end() {
        assert!(
            Definitions::new()
                .compile("each(introduce { pick 0")
                .is_err()
        );
    }

    // -- reading a rule backwards --------------------------------------------

    #[test]
    fn inv_names_the_backward_reading_of_any_rule() {
        assert!(compiles("each(inv(fuse))"));
        assert!(compiles("once(inv(distribute))"));
        assert!(compiles("at(2, inv(unfactor))"));
        // Where the backward reading has a name of its own, `inv` is that name.
        assert!(compiles("each(inv(sink))"));
        // Twice over is forwards again, which is worth allowing rather than
        // special-casing: a definition may already say `inv`.
        assert!(compiles("each(inv(inv(sink)))"));
        // Alongside ordinary rules in one placement, and over a term rule.
        assert!(compiles("each(collapse, inv(fuse), sink)"));
        assert!(compiles("once(inv(introduce { pick 0 }))"));
    }

    #[test]
    fn a_rule_may_be_narrowed_by_a_number() {
        assert!(compiles("each(counit(0))"));
        assert!(compiles("at(2, inv(counit(0)))"));
        assert!(compiles("each(collapse, counit(3), sink)"));
        // The number is what makes the backward reading writable at all.
        let e = err("each(inv(counit))");
        assert!(e.contains("inv(counit(0))"), "{}", e);
    }

    #[test]
    fn a_number_is_only_accepted_where_a_rule_takes_one() {
        assert!(err("each(counit(0, 1))").contains("takes one number"));
        assert!(err("each(counit())").contains("takes one number"));
        assert!(err("each(counit(sink))").contains("takes one number"));
        let e = err("each(sink(0))");
        assert!(e.contains("unknown rule form"), "{}", e);
        assert!(e.contains("counit"), "{}", e);
    }

    #[test]
    fn a_rule_with_no_backward_reading_says_what_stands_in_the_way() {
        // Three different reasons, and the message is the whole point of
        // refusing here rather than matching nothing at run time.
        let e = err("each(inv(eval1))");
        assert!(e.contains("no backward reading"), "{}", e);
        assert!(e.contains("invent the operator"), "{}", e);

        let e = err("each(inv(cancel_tuple))");
        assert!(e.contains("does not say what `n` was"), "{}", e);

        // And one that points at the rule that *does* do the job.
        let e = err("each(inv(annihilate))");
        assert!(e.contains("introduce {"), "{}", e);
        let e = err("each(inv(factor))");
        assert!(e.contains("inv(unfactor)"), "{}", e);
    }

    #[test]
    fn inv_is_a_rule_and_still_has_to_be_placed() {
        let e = err("inv(fuse)");
        assert!(e.contains("is a rule, not a tactic"), "{}", e);
        assert!(e.contains("each(inv(fuse))"), "{}", e);
    }

    #[test]
    fn inv_takes_exactly_one_rule() {
        assert!(err("each(inv())").contains("exactly one rule"));
        assert!(err("each(inv(sink, fuse))").contains("exactly one rule"));
        assert!(err("each(inv(nope))").contains("unknown rule 'nope'"));
        // Any other call in rule position is not a rule form at all.
        assert!(err("each(nope(sink))").contains("unknown rule form"));
    }

    #[test]
    fn inv_may_not_be_taken_as_a_tactic_name() {
        let mut d = defs();
        let e = d.load("tactic inv = id;").unwrap_err();
        assert!(e.message.contains("backward-reading form"), "{}", e.message);
    }

    // -- aiming -------------------------------------------------------------

    #[test]
    fn at_takes_a_position_and_then_rules() {
        assert!(compiles("at(0, sink)"));
        assert!(compiles("at(3, sink, fuse)"));
        assert!(compiles("at(1, introduce { pick 0 })"));
        assert!(compiles("bu(at(0, collapse))"));
    }

    #[test]
    fn at_without_a_position_says_what_it_wants() {
        let e = err("at(sink)");
        assert!(e.contains("a position and then rules"), "{}", e);
        assert!(e.contains("at(2, sink)"), "{}", e);
    }

    #[test]
    fn at_still_insists_on_a_rule() {
        assert!(err("at(0)").contains("at least one rule"));
    }

    #[test]
    fn a_descent_reaches_every_child_or_one() {
        assert!(compiles("then(each(sink))"));
        assert!(compiles("then(2, each(sink))"));
        assert!(compiles("else(0, at(1, fuse))"));
        assert!(compiles("body(7, id)"));
        // Nested, which is how a whole path gets written.
        assert!(compiles("then(1, body(2, at(0, sink)))"));
    }

    #[test]
    fn a_descent_given_nonsense_explains_both_readings() {
        let e = err("then(1, 2)");
        assert!(e.contains("a tactic, or an index and a tactic"), "{}", e);
        assert!(e.contains("reaches every one"), "{}", e);
    }

    #[test]
    fn must_guards_an_aimed_step() {
        assert!(compiles("must(at(2, sink))"));
        assert!(compiles("must(then(1, once(collapse)))"));
        assert!(compiles("try(must(at(0, fuse)))"));
        assert!(err("must(1, at(0, sink))").contains("exactly one tactic"));
    }

    #[test]
    fn the_traversals_that_take_no_index_still_do_not() {
        // `bu`, `td`, `children` visit everything by their nature; an index
        // would mean nothing, so it is refused rather than ignored.
        assert!(err("bu(1, each(sink))").contains("exactly one tactic"));
        assert!(err("children(1, each(sink))").contains("exactly one tactic"));
    }

    // -----------------------------------------------------------------------
    // `.hant`: proofs out of line
    // -----------------------------------------------------------------------

    /// A tiny corpus, so a proof has a program to be compiled against.
    fn corpus(source: &str) -> bytecode::Library {
        bytecode::assemble(source).unwrap_or_else(|e| panic!("{}", e))
    }

    fn hant(library: &bytecode::Library, source: &str) -> Result<ProofFile, String> {
        let prog = Program::new(library);
        ProofFile::parse(source, &defs(), &prog).map_err(|e| e.render_in(source, "x.hant"))
    }

    /// The rendered error, or a panic if the file was fine after all.
    fn hant_err(library: &bytecode::Library, source: &str) -> String {
        match hant(library, source) {
            Err(rendered) => rendered,
            Ok(_) => panic!("expected an error from:\n{}", source),
        }
    }

    /// The same, for a `.hant` that parses but whose proof will not resolve.
    fn proof_err(library: &bytecode::Library, source: &str) -> String {
        let prog = Program::new(library);
        let file = hant(library, source).expect("parses");
        match file.compile(&file.proofs[0], &prog) {
            Err(e) => e.render_in(source, "x.hant"),
            Ok(_) => panic!("expected a resolution error from:\n{}", source),
        }
    }

    #[test]
    fn a_hant_holds_tactics_and_proofs_together() {
        let lib = corpus("identity foo { is_bool is_bool } = { drop 0 push true };");
        let file =
            hant(&lib, "tactic mine = cleanup; values;\nproof foo = mine;\n").expect("parses");
        assert_eq!(file.proofs.len(), 1);
        assert_eq!(file.proofs[0].path, "foo");
        assert!(file.defs.names().contains(&"mine".to_string()));
    }

    #[test]
    fn a_proof_may_name_a_qualified_identity() {
        let lib = corpus("mod m { identity foo { drop 0 } = { drop 0 }; }");
        let file = hant(&lib, "proof m::foo = id;").expect("parses");
        assert_eq!(file.proofs[0].path, "m::foo");
    }

    #[test]
    fn a_proof_body_is_a_whole_tactic_expression() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let file = hant(&lib, "proof foo = (cleanup; values) | id;").expect("parses");
        let prog = Program::new(&lib);
        file.compile(&file.proofs[0], &prog).expect("compiles");
    }

    /// A tactic name shadows, because the prelude is meant to be overridable.
    /// A proof does not: a claim discharged twice was discharged once too often.
    #[test]
    fn two_proofs_of_one_identity_are_refused() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let rendered = hant_err(&lib, "proof foo = id;\nproof foo = cleanup;\n");
        assert!(rendered.contains("proved twice"), "{}", rendered);
        assert!(rendered.contains("x.hant:2:7"), "{}", rendered);
    }

    #[test]
    fn a_tactic_name_still_shadows() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let file =
            hant(&lib, "tactic t = id;\ntactic t = cleanup;\nproof foo = t;").expect("parses");
        assert_eq!(file.proofs.len(), 1);
    }

    #[test]
    fn proof_is_refused_in_a_tactics_file() {
        let mut d = defs();
        let source = "proof foo = id;";
        let rendered = d
            .load(source)
            .expect_err("expected an error")
            .render_in(source, "extra.tactics");
        assert!(
            rendered.contains("`proof` is not a tactic definition"),
            "{}",
            rendered
        );
        assert!(rendered.contains("belongs in the `.hant`"), "{}", rendered);
    }

    /// The trap this shape exists to avoid: compiling each proof from its own
    /// substring would tokenize from offset 0, so every error in every `.hant`
    /// would report line 1.
    #[test]
    fn an_error_in_a_proof_points_at_its_line_in_the_file() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let source = "tactic t = id;\n\nproof foo = nonesuch;\n";
        let rendered = proof_err(&lib, source);
        assert!(rendered.contains("x.hant:3:13"), "{}", rendered);
        assert!(rendered.contains("unknown tactic"), "{}", rendered);
    }

    /// A term in a `.hant` may name a sentence, where one in a `--tactics`
    /// file may not — the difference being that a `.hant` is only ever read
    /// once a corpus has been chosen.
    #[test]
    fn a_proof_may_name_a_sentence_in_a_term() {
        let lib = corpus(
            "#[total] function classify { pick 0 is_int branch { drop 0 push 7 } { drop 0 push 8 } }\n\
             identity foo { drop 0 } = { drop 0 };",
        );
        hant(&lib, "proof foo = try(once(share { jump classify }));").expect("parses");
    }

    // -----------------------------------------------------------------------
    // The strategy language
    // -----------------------------------------------------------------------

    /// One grammar, two languages, and the deciding question is which table a
    /// name resolves against.
    #[test]
    fn a_proof_naming_no_strategy_is_still_a_tactic() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let prog = Program::new(&lib);
        for source in [
            "proof foo = cleanup;",
            // `;` and `|` and the combinators all keep their tactic reading,
            // which is what makes this change invisible to every `.hant` that
            // came before it.
            "proof foo = dips; cleanup;",
            "proof foo = try(at(9, sink)) | id;",
            "proof foo = then(cleanup);",
        ] {
            let file = hant(&lib, source).expect("parses");
            let compiled = file
                .compile(&file.proofs[0], &prog)
                .unwrap_or_else(|e| panic!("{}", e.render_in(source, "x.hant")));
            assert!(
                matches!(compiled, Strategy::Blind(_)),
                "`{}` should read as a blind tactic",
                source
            );
        }
    }

    /// ...and `then` keeps meaning the traversal, not the goal-descent. Two
    /// readings of one word would be a trap, so the descent is spelled
    /// `descend(then: ...)` and nothing collides.
    #[test]
    fn the_descent_does_not_take_a_traversals_name() {
        assert!(
            COMBINATORS.iter().all(|(n, _)| !STRATEGY_FORMS.contains(n)),
            "a strategy form shares a name with a tactic combinator"
        );
    }

    /// Moves sequence, which is the whole point of their being moves: each
    /// rewrites one side and leaves a goal for the next.
    #[test]
    fn moves_sequence_with_a_semicolon() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        for source in [
            "proof foo = cleanup; rhs(dips);",
            "proof foo = exact(cleanup); rhs(unfold_all);",
            "proof foo = rhs(dips); rhs(cleanup); normalize(all);",
        ] {
            let prog = Program::new(&lib);
            let file = hant(&lib, source).expect("parses");
            let compiled = file
                .compile(&file.proofs[0], &prog)
                .unwrap_or_else(|e| panic!("{}", e.render_in(source, "x.hant")));
            assert!(matches!(compiled, Strategy::Sequence { .. }), "{}", source);
        }
    }

    #[test]
    fn descend_takes_its_parts_by_name() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let rendered = proof_err(&lib, "proof foo = descend(cleanup);");
        assert!(rendered.contains("takes named parts"), "{}", rendered);

        let rendered = proof_err(&lib, "proof foo = descend(arm: cleanup);");
        assert!(rendered.contains("not a part a node has"), "{}", rendered);

        let rendered = proof_err(&lib, "proof foo = descend(then: id, then: id);");
        assert!(rendered.contains("given twice"), "{}", rendered);

        let rendered = proof_err(&lib, "proof foo = descend(body: id, then: id);");
        assert!(
            rendered.contains("mixes a body with branch arms"),
            "{}",
            rendered
        );
    }

    /// A frame has a body and a branch has two arms, and no node has both — so
    /// the two shapes are the two forms, and each resolves.
    #[test]
    fn both_shapes_of_descend_resolve() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        for source in [
            "proof foo = descend(body: cleanup);",
            "proof foo = descend(then: cleanup, else: dips);",
            // One arm named is the claim that the other needs no proof.
            "proof foo = descend(then: cleanup);",
            "proof foo = peel ; descend(then: normalize(all));",
            "proof foo = inline ; exact(cleanup);",
        ] {
            let prog = Program::new(&lib);
            let file = hant(&lib, source).expect("parses");
            file.compile(&file.proofs[0], &prog)
                .unwrap_or_else(|e| panic!("{}", e.render_in(source, "x.hant")));
        }
    }

    /// Three namespaces, and a name in two of them would not say which layer it
    /// belonged to.
    #[test]
    fn a_strategy_may_not_take_a_name_that_is_taken() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let rendered = hant_err(&lib, "strategy cleanup = normalize(all);\nproof foo = id;");
        assert!(rendered.contains("already a name"), "{}", rendered);

        let rendered = hant_err(&lib, "strategy peel = normalize(all);\nproof foo = id;");
        assert!(rendered.contains("is a strategy form"), "{}", rendered);

        let rendered = hant_err(
            &lib,
            "strategy mine = normalize(all);\ntactic mine = cleanup;\nproof foo = id;",
        );
        assert!(rendered.contains("is a strategy name"), "{}", rendered);
    }

    /// The rule tactics are held to, for the reason tactics are held to it:
    /// nothing here measures a goal getting smaller, so the depth is written.
    #[test]
    fn a_strategy_may_not_recurse() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let rendered = proof_err(&lib, "strategy loop = peel ; loop;\nproof foo = loop;");
        assert!(
            rendered.contains("defined in terms of itself"),
            "{}",
            rendered
        );
        assert!(rendered.contains("no measure"), "{}", rendered);
    }

    #[test]
    fn a_hant_that_is_not_a_definition_says_so() {
        let lib = corpus("identity foo { drop 0 } = { drop 0 };");
        let rendered = hant_err(&lib, "cleanup;");
        assert!(
            rendered.contains("expected 'tactic', 'strategy' or 'proof'"),
            "{}",
            rendered
        );
    }
}
