//! The derivation format: a script, written down.
//!
//! A [`Script`][crate::rule::Script] is a derivation the tool holds in memory,
//! and until this existed it could only be *printed* — as a listing, for a
//! person, in a shape nothing could read back. So a derivation could not leave
//! the process that found it, and the only way to obtain one was to run the
//! search that produces it. This is the same derivation as bytes.
//!
//! ## What it is for
//!
//! **Finding a proof and checking one are different jobs, and only the second
//! has to be trusted.** A generator may be a tactic script, a solver, a
//! program in another language, or a person with a text editor; what it hands
//! over is a file in this format, and [`crate::replay`] decides. That is why
//! the format is the deliverable rather than the search: one checker, many
//! producers.
//!
//! ## What portability costs, and what it buys
//!
//! Three things a `Step` holds in memory are meaningless outside the process
//! that built it, and each is dealt with rather than written down:
//!
//! - **A `SentenceIndex` is an offset into one assembly of one corpus.** It is
//!   written as the sentence's fully qualified name, and the printer refuses a
//!   name that does not resolve back to the sentence it came from rather than
//!   emitting one that would silently mean something else.
//! - **A `Symbol` compares by `id`**, which is minted during assembly. It is
//!   written as its declared path and looked up on the way back in, exactly as
//!   a term in a tactic does it.
//! - **Provenance is not part of a term's identity.** `Dip::origins` and a
//!   branch's arm labels say where code came from, which is for a listing;
//!   [`crate::ir::same_effect`] ignores them and so does everything that reads
//!   a replayed tree. They are dropped, and what a parsed step rebuilds carries
//!   [`TERM_ORIGIN`] — the label a block written by hand already gets.
//!
//! What is *not* dealt with, on purpose, is program content. A step names a
//! sentence and never quotes it, so an `unfold` here is three words no matter
//! how large the body it opens, and a file written against a library that has
//! since changed fails at the step that stopped fitting rather than rewriting
//! by a stale copy.
//!
//! ## The grammar
//!
//! ```text
//! file    := "derivation" INT ";" proof*
//! proof   := "proof" path "{" step* "}"
//! step    := ident args? arrow location ";"
//! args    := "(" ident "=" value ("," ident "=" value)* ")"
//! arrow   := "->" | "<-"
//! location:= descent? "@" INT
//! descent := "[" INT "." kind ("," INT "." kind)* "]"
//! kind    := "then" | "else" | "body"
//! value   := INT | STRING | ident INT? | term | list | tuple
//! term    := "{" instruction* "}"
//! list    := "[" (value ("," value)*)? "]"
//! tuple   := "(" (value ("," value)*)? ")"
//! ```
//!
//! Arguments are **named**, not positional. A wire format is read by people
//! debugging a generator that got one of them wrong, and `annihilate(x = { add
//! }, n = 2, m = 2)` says which number is which where `annihilate({ add }, 2,
//! 2)` needs the reader to know. It also means the checker can say `annihilate`
//! needs `n` instead of counting.
//!
//! An instruction inside a term is spelled as a tactic's term spells it — see
//! [`crate::script`], whose vocabulary this shares rather than restates. Two
//! things are written here that a tactic cannot write, because a derivation may
//! hold them and a hand-written term never needed to: a call at depth, as `dip
//! k <sentence>` beside the `jump <sentence>` that is one at depth 0, and the
//! one literal shape a corpus can hold but a tactic had no syntax for —
//! tuples.

use bytecode::{Instruction, SentenceIndex, Value};

use crate::ir::{Node, Selector};
use crate::location::Location;
use crate::program::{Program, resolve_sentence, resolve_symbol};
use crate::rule::{Arm, Direction, Rule, Step, StepKind};
use crate::script::{ScriptError, Span, TERM_ORIGIN, plain_instruction, plain_word};

/// The format version this build reads and writes.
///
/// A file says which version it is in its first statement, so a checker meeting
/// a format it does not know says so instead of guessing at the parts it
/// recognizes. That is the whole of the compatibility story: there is no
/// negotiation and no partial reading.
pub(crate) const VERSION: i64 = 1;

/// The extension a derivation file conventionally has.
pub(crate) const EXTENSION: &str = "hand";

/// One `proof <identity> { ... }`: a derivation, and what it claims.
///
/// The identity is a name rather than an [`bytecode::IdentityIndex`] for the
/// same reason a sentence is: an index is a fact about one assembly. Resolving
/// it is [`crate::replay`]'s job, since a parse should not need a corpus to
/// have stated anything in particular.
#[derive(Debug)]
pub(crate) struct Derivation {
    pub(crate) identity: String,
    /// Where the name was written, for an error that has to point at it.
    pub(crate) identity_span: Span,
    pub(crate) steps: Vec<Step>,
    /// One span per step, parallel to `steps`. A replay that fails at step 7
    /// can then underline step 7 in the file rather than counting for the
    /// reader.
    pub(crate) step_spans: Vec<Span>,
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// A whole file: the version, then one block per derivation.
///
/// The error is a sentence about why this derivation cannot be written down.
/// There are only two causes — a sentence or a symbol whose name does not
/// resolve back to it — and both mean the file would say something other than
/// what the script does, which is worse than not writing it.
pub(crate) fn write(prog: &Program, proofs: &[(&str, &[Step])]) -> Result<String, String> {
    let mut out = format!("derivation {};\n", VERSION);
    for (name, steps) in proofs {
        out.push('\n');
        out.push_str(&format!("proof {} {{\n", name));
        for step in *steps {
            out.push_str(&format!("    {}\n", write_step(prog, step)?));
        }
        out.push_str("}\n");
    }
    Ok(out)
}

/// One step, terminated: `annihilate(x = { is_bool }, n = 1, m = 1) -> @0;`
///
/// The direction and the location are spelled exactly as `--show-script`
/// spells them, so a step read off a listing and a step read out of a file are
/// the same text. What the listing does not say is the arguments, which is the
/// difference between a description of a derivation and the derivation.
pub(crate) fn write_step(prog: &Program, step: &Step) -> Result<String, String> {
    Ok(format!(
        "{} {} {};",
        write_kind(prog, &step.kind)?,
        step.dir.arrow(),
        step.loc
    ))
}

fn write_kind(prog: &Program, kind: &StepKind) -> Result<String, String> {
    let args = match kind {
        StepKind::Unfold { depth, target } => vec![
            ("depth", depth.to_string()),
            ("target", write_sentence(prog, *target)?),
        ],
        StepKind::Rule(rule) => write_rule(prog, rule)?,
    };
    if args.is_empty() {
        return Ok(kind.name().to_string());
    }
    let body: Vec<String> = args
        .iter()
        .map(|(name, value)| format!("{} = {}", name, value))
        .collect();
    Ok(format!("{}({})", kind.name(), body.join(", ")))
}

/// Every equation's arguments, in the order [`arg_names`] lists them.
///
/// Exhaustive on purpose: adding an equation is adding an axiom, and this is
/// the line that makes the compiler ask whether the new one can be written
/// down. A rule whose arguments cannot cross a process boundary is a rule no
/// generator can ask for.
fn write_rule(prog: &Program, rule: &Rule) -> Result<Vec<(&'static str, String)>, String> {
    Ok(match rule {
        // Provenance is absent from every one of these. `outer`/`inner`,
        // `origins`, `a_origins`/`b_origins` and the two arm labels say where
        // code came from, which no reader of a replayed tree consults.
        Rule::Collapse { k, j, a, .. } => vec![
            ("k", k.to_string()),
            ("j", j.to_string()),
            ("a", write_term(prog, a)?),
        ],
        Rule::ElimDip0 { a, .. } => vec![("a", write_term(prog, a)?)],
        Rule::Interchange { x, framed, n, m } => vec![
            ("x", write_term(prog, std::slice::from_ref(x))?),
            ("framed", write_term(prog, std::slice::from_ref(framed))?),
            ("n", n.to_string()),
            ("m", m.to_string()),
        ],
        Rule::Fuse { k, a, b, .. } => vec![
            ("k", k.to_string()),
            ("a", write_term(prog, a)?),
            ("b", write_term(prog, b)?),
        ],
        Rule::Hoist {
            k,
            x,
            then_arm,
            else_arm,
            ..
        } => vec![
            ("k", k.to_string()),
            ("x", write_term(prog, x)?),
            ("then", write_term(prog, then_arm)?),
            ("else", write_term(prog, else_arm)?),
        ],
        Rule::Distribute {
            then_arm,
            else_arm,
            suffix,
            ..
        } => vec![
            ("then", write_term(prog, then_arm)?),
            ("else", write_term(prog, else_arm)?),
            ("suffix", write_term(prog, suffix)?),
        ],
        Rule::FoldBranch {
            c,
            then_arm,
            else_arm,
            ..
        } => vec![
            ("c", write_value(prog, c)?),
            ("then", write_term(prog, then_arm)?),
            ("else", write_term(prog, else_arm)?),
        ],
        Rule::Eval { op, inputs } => {
            let values: Result<Vec<String>, String> =
                inputs.iter().map(|v| write_value(prog, v)).collect();
            vec![
                ("op", write_op(prog, op)?),
                ("inputs", format!("[{}]", values?.join(", "))),
            ]
        }
        Rule::Annihilate { x, n, m } => vec![
            ("x", write_term(prog, x)?),
            ("n", n.to_string()),
            ("m", m.to_string()),
        ],
        Rule::Commute { op } => vec![("op", write_op(prog, op)?)],
        Rule::SplitBool => Vec::new(),
        Rule::Counit { d } => vec![("d", d.to_string())],
        Rule::CounitUnder => Vec::new(),
        Rule::Retest {
            arm,
            inner,
            rest,
            other,
            ..
        } => vec![
            ("arm", arm.name().to_string()),
            ("inner", write_term(prog, std::slice::from_ref(inner))?),
            ("rest", write_term(prog, rest)?),
            ("other", write_term(prog, other)?),
        ],
        Rule::SpecializeEqual {
            c,
            then_arm,
            else_arm,
            ..
        } => vec![
            ("c", write_value(prog, c)?),
            ("then", write_term(prog, then_arm)?),
            ("else", write_term(prog, else_arm)?),
        ],
        Rule::CopyConst { c } => vec![("c", write_value(prog, c)?)],
        Rule::CopyAssoc { d } => vec![("d", d.to_string())],
        Rule::CopyNat { x, n, m } => vec![
            ("x", write_term(prog, x)?),
            ("n", n.to_string()),
            ("m", m.to_string()),
        ],
        Rule::BoolResult { op } => vec![("op", write_op(prog, op)?)],
        Rule::CancelTuple { n } => vec![("n", n.to_string())],
        Rule::RollCycle { d } => vec![("d", d.to_string())],
        Rule::Unframe { framed, n, m } => vec![
            ("framed", write_term(prog, std::slice::from_ref(framed))?),
            ("n", n.to_string()),
            ("m", m.to_string()),
        ],
        Rule::PickRoll { d } => vec![("d", d.to_string())],
    })
}

/// A braced run of instructions. `{ }` is a term that holds nothing, which
/// several equations legitimately have — `annihilate` at `m = 0` reads a
/// `branch { } { }`.
fn write_term(prog: &Program, nodes: &[Node]) -> Result<String, String> {
    let mut parts = Vec::new();
    for node in nodes {
        parts.push(write_node(prog, node)?);
    }
    if parts.is_empty() {
        return Ok("{ }".to_string());
    }
    Ok(format!("{{ {} }}", parts.join(" ")))
}

fn write_node(prog: &Program, node: &Node) -> Result<String, String> {
    Ok(match node {
        Node::Op(inst) => write_op(prog, inst)?,
        // A plain jump and a call that hides something are one instruction in
        // the ISA and are spelled as two words here, the way the surface
        // language spells them.
        Node::Call { depth: 0, target } => format!("jump {}", write_sentence(prog, *target)?),
        Node::Call { depth, target } => {
            format!("dip {} {}", depth, write_sentence(prog, *target)?)
        }
        Node::Dip { depth, body, .. } => format!("dip {} {}", depth, write_term(prog, body)?),
        Node::Branch {
            then_body,
            else_body,
            ..
        } => format!(
            "branch {} {}",
            write_term(prog, then_body)?,
            write_term(prog, else_body)?
        ),
    })
}

fn write_op(prog: &Program, inst: &Instruction) -> Result<String, String> {
    Ok(match inst {
        Instruction::Pick(d) => format!("pick {}", d),
        Instruction::Roll(d) => format!("roll {}", d),
        Instruction::Tuple(n) => format!("tuple {}", n),
        Instruction::Untuple(n) => format!("untuple {}", n),
        Instruction::Push(v) => format!("push {}", write_value(prog, v)?),
        other => match plain_word(other) {
            Some(word) => word.to_string(),
            None => {
                return Err(format!(
                    "`{}` is not an instruction a derivation may name",
                    other
                ));
            }
        },
    })
}

/// A literal, with the program in hand so a symbol can be checked.
fn write_value(prog: &Program, value: &Value) -> Result<String, String> {
    match value {
        // A symbol is its identity, not its text: two declarations reading the
        // same are different symbols. So the path is only a *way to find* the
        // one meant, and writing it down is worth nothing unless reading it
        // back finds the same one. This is where that is checked.
        Value::Symbol(sym) => match resolve_symbol(prog.library(), &sym.path) {
            Ok(found) if found == *value => Ok(sym.path.clone()),
            _ => Err(format!(
                "the symbol `{}` does not resolve to itself by name, so a \
                 derivation naming it would mean something else",
                sym.path
            )),
        },
        Value::Tuple(elements) => {
            let mut parts = Vec::new();
            for element in elements {
                parts.push(write_value(prog, element)?);
            }
            Ok(match parts.len() {
                // `(x)` is parenthesization in every language that has tuples;
                // the trailing comma is what makes it a one-element tuple, and
                // `Value`'s own listing already prints it that way.
                1 => format!("({},)", parts[0]),
                _ => format!("({})", parts.join(", ")),
            })
        }
        other => write_bare_value(other),
    }
}

/// The literals that need nothing looked up, which is every one whose text
/// *is* the value.
fn write_bare_value(value: &Value) -> Result<String, String> {
    Ok(match value {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        // The same escape-free strings `.hana` has, so a quote inside one has
        // no spelling in either language.
        Value::ConstString(s) if !s.contains('"') => format!("{:?}", s),
        Value::ConstString(_) => {
            return Err("a const string holding a `\"` cannot be written down".to_string());
        }
        // The two that need the library are handled by `write_value`, which
        // is the only caller: a symbol has to be looked up and a tuple may
        // hold one.
        Value::Symbol(_) | Value::Tuple(_) => {
            unreachable!("write_value handles the values that need a program")
        }
    })
}

/// The sentence's fully qualified name, held to naming it.
///
/// [`resolve_sentence`] reads an exact name, an unambiguous trailing part of
/// one, or an index. What it will not do is invent one, so a sentence the
/// library gives a name that means something else — or nothing — is refused
/// here rather than written into a file that would replay somewhere else.
/// This is unreachable in practice: an unnamed `<inline>` block is expanded
/// where it is met rather than left as a `Call`, so a `Call` always names a
/// sentence somebody wrote.
fn write_sentence(prog: &Program, target: SentenceIndex) -> Result<String, String> {
    let name = &prog.library().names[target];
    match resolve_sentence(prog.library(), name) {
        Ok(found) if found == target => Ok(name.clone()),
        _ => Err(format!(
            "sentence #{} is named `{}`, which does not resolve back to it, so \
             a derivation naming it would mean something else",
            usize::from(target),
            name
        )),
    }
}

// ---------------------------------------------------------------------------
// Tokenizing
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    Int(i64),
    Str(String),
    /// `->` or `<-`.
    Arrow(Direction),
    Dash,
    At,
    Dot,
    Comma,
    Semi,
    Eq,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
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
        if c == '/' && bytes.get(i + 1) == Some(&b'/') {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        let start = i;
        let tok = match c {
            '-' if bytes.get(i + 1) == Some(&b'>') => {
                i += 2;
                Tok::Arrow(Direction::Forward)
            }
            '<' if bytes.get(i + 1) == Some(&b'-') => {
                i += 2;
                Tok::Arrow(Direction::Reverse)
            }
            '-' => {
                i += 1;
                Tok::Dash
            }
            '@' => {
                i += 1;
                Tok::At
            }
            '.' => {
                i += 1;
                Tok::Dot
            }
            ',' => {
                i += 1;
                Tok::Comma
            }
            ';' => {
                i += 1;
                Tok::Semi
            }
            '=' => {
                i += 1;
                Tok::Eq
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
            '[' => {
                i += 1;
                Tok::LBracket
            }
            ']' => {
                i += 1;
                Tok::RBracket
            }
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
                i += 1;
                Tok::Str(text)
            }
            c if c.is_ascii_digit() => number(src, bytes, &mut i, start)?,
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
                // `::` continues the same token, so a sentence, a symbol and an
                // identity are all named the way the rest of the tool names
                // them.
                while src[i..].starts_with("::") {
                    i += 2;
                    word(&mut i);
                }
                Tok::Ident(src[start..i].to_string())
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

/// An integer, which is the only number the language has.
fn number(src: &str, bytes: &[u8], i: &mut usize, start: usize) -> Result<Tok, ScriptError> {
    while *i < bytes.len() && (bytes[*i] as char).is_ascii_digit() {
        *i += 1;
    }
    let text = &src[start..*i];
    text.parse::<i64>()
        .map(Tok::Int)
        .map_err(|_| ScriptError::new(format!("'{}' is too large a number", text), (start, *i)))
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// Reads a whole file. Every step is checked for shape here and for truth by
/// the applier, which is the division of labour the format rests on: parsing
/// says a step is *well formed*, and nothing more.
pub(crate) fn parse(source: &str, prog: &Program) -> Result<Vec<Derivation>, ScriptError> {
    let toks = tokenize(source)?;
    let mut p = Parser {
        toks: &toks,
        pos: 0,
        end: source.len(),
        prog,
    };
    p.file()
}

struct Parser<'a> {
    toks: &'a [Spanned],
    pos: usize,
    end: usize,
    prog: &'a Program<'a>,
}

/// An argument's value, before it is read as the kind its slot wants.
///
/// One grammar for every argument and a type-directed reading afterwards, so
/// `n = { add }` is "`n` must be a count" rather than a parse error about a
/// brace. Which is the useful message: the generator that wrote it knows what
/// it meant to say.
enum Val {
    /// A bare word, optionally followed by a count: `add`, `untuple 2`,
    /// `then`, `queue::accept`.
    Word(String, Option<i64>, Span),
    Int(i64, Span),
    Str(String, Span),
    Term(Vec<Node>, Span),
    List(Vec<Val>, Span),
    Tuple(Vec<Val>, Span),
}

impl Val {
    fn span(&self) -> Span {
        match self {
            Val::Word(_, _, s)
            | Val::Int(_, s)
            | Val::Str(_, s)
            | Val::Term(_, s)
            | Val::List(_, s)
            | Val::Tuple(_, s) => *s,
        }
    }

    fn describe(&self) -> &'static str {
        match self {
            Val::Word(..) => "a word",
            Val::Int(..) => "an integer",
            Val::Str(..) => "a string",
            Val::Term(..) => "a term",
            Val::List(..) => "a list",
            Val::Tuple(..) => "a tuple",
        }
    }
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

    fn ident(&mut self, what: &str) -> Result<(String, Span), ScriptError> {
        let span = self.span();
        match self.bump() {
            Some(Spanned {
                tok: Tok::Ident(name),
                ..
            }) => Ok((name.clone(), span)),
            Some(other) => Err(ScriptError::new(
                format!("expected {}, found {}", what, describe(&other.tok)),
                span,
            )),
            None => Err(ScriptError::new(
                format!("expected {}, found end of input", what),
                span,
            )),
        }
    }

    fn count(&mut self, what: &str) -> Result<i64, ScriptError> {
        let span = self.span();
        match self.bump() {
            Some(Spanned {
                tok: Tok::Int(n), ..
            }) => Ok(*n),
            Some(other) => Err(ScriptError::new(
                format!("expected {}, found {}", what, describe(&other.tok)),
                span,
            )),
            None => Err(ScriptError::new(
                format!("expected {}, found end of input", what),
                span,
            )),
        }
    }

    fn file(&mut self) -> Result<Vec<Derivation>, ScriptError> {
        let (word, span) = self.ident("`derivation`")?;
        if word != "derivation" {
            return Err(
                ScriptError::new(format!("expected `derivation`, found '{}'", word), span)
                    .with_help(format!(
                        "a derivation file opens with its format version: `derivation {};`",
                        VERSION
                    )),
            );
        }
        let version_span = self.span();
        let version = self.count("the format version")?;
        if version != VERSION {
            return Err(ScriptError::new(
                format!("this file is in derivation format {}", version),
                version_span,
            )
            .with_help(format!(
                "this tool reads format {}. A version it does not know is refused \
                 rather than read as far as it happens to parse",
                VERSION
            )));
        }
        self.expect(Tok::Semi, "';'")?;

        let mut out = Vec::new();
        while self.peek().is_some() {
            out.push(self.derivation()?);
        }
        Ok(out)
    }

    fn derivation(&mut self) -> Result<Derivation, ScriptError> {
        let (word, span) = self.ident("`proof`")?;
        if word != "proof" {
            return Err(
                ScriptError::new(format!("expected `proof`, found '{}'", word), span).with_help(
                    "a derivation file holds `proof <identity> { <step>* }` blocks \
                     and nothing else",
                ),
            );
        }
        let (identity, identity_span) = self.ident("the name of an identity")?;
        self.expect(Tok::LBrace, "'{'")?;

        let mut steps = Vec::new();
        let mut step_spans = Vec::new();
        while !matches!(self.peek(), Some(&Tok::RBrace) | None) {
            let (step, span) = self.step()?;
            steps.push(step);
            step_spans.push(span);
        }
        self.expect(Tok::RBrace, "'}' or a step")?;

        Ok(Derivation {
            identity,
            identity_span,
            steps,
            step_spans,
        })
    }

    fn step(&mut self) -> Result<(Step, Span), ScriptError> {
        let (name, name_span) = self.ident("the name of an equation")?;
        let mut fields = Fields {
            rule: name.clone(),
            span: name_span,
            args: Vec::new(),
        };
        if self.peek() == Some(&Tok::LParen) {
            self.bump();
            if self.peek() != Some(&Tok::RParen) {
                loop {
                    let (arg, arg_span) = self.ident("an argument name")?;
                    if let Some((_, prior, _)) = fields.args.iter().find(|(n, _, _)| *n == arg) {
                        return Err(ScriptError::new(
                            format!("`{}` is given twice", arg),
                            arg_span,
                        )
                        .with_help(format!(
                            "the first is at byte {}; an argument is written once",
                            prior.0
                        )));
                    }
                    self.expect(Tok::Eq, "'='")?;
                    let value = self.value()?;
                    fields.args.push((arg, arg_span, value));
                    if self.peek() == Some(&Tok::Comma) {
                        self.bump();
                        continue;
                    }
                    break;
                }
            }
            self.expect(Tok::RParen, "')' or ','")?;
        }

        let dir_span = self.span();
        let dir = match self.bump() {
            Some(Spanned {
                tok: Tok::Arrow(dir),
                ..
            }) => *dir,
            _ => {
                return Err(
                    ScriptError::new("expected `->` or `<-`", dir_span).with_help(
                        "a step says which way its equation is read: `->` finds the \
                         left-hand side and leaves the right, `<-` the other way",
                    ),
                );
            }
        };
        let loc = self.location()?;
        let end = self.expect(Tok::Semi, "';'")?;

        let kind = self.kind(fields)?;
        Ok((Step { kind, dir, loc }, (name_span.0, end.1)))
    }

    /// `[1.then, 2.body] @2`, read outermost-first — the same text a listing
    /// prints, so a location can be copied from one to the other.
    fn location(&mut self) -> Result<Location, ScriptError> {
        let mut descent = Vec::new();
        if self.peek() == Some(&Tok::LBracket) {
            self.bump();
            if self.peek() != Some(&Tok::RBracket) {
                loop {
                    let index = self.count("an index")?;
                    let index = usize::try_from(index).map_err(|_| {
                        ScriptError::new("an index may not be negative", self.span())
                    })?;
                    self.expect(Tok::Dot, "'.'")?;
                    let (kind, kind_span) = self.ident("`then`, `else` or `body`")?;
                    let sel = match kind.as_str() {
                        "then" => Selector::Then,
                        "else" => Selector::Else,
                        "body" => Selector::Body,
                        other => {
                            return Err(ScriptError::new(
                                format!("'{}' is not a part of a node", other),
                                kind_span,
                            )
                            .with_help(
                                "a descent turns into the `then` or `else` arm of a \
                                 branch, or the `body` of a dip",
                            ));
                        }
                    };
                    descent.push((index, sel));
                    if self.peek() == Some(&Tok::Comma) {
                        self.bump();
                        continue;
                    }
                    break;
                }
            }
            self.expect(Tok::RBracket, "']' or ','")?;
        }
        self.expect(Tok::At, "'@' and the offset the window starts at")?;
        let at_span = self.span();
        let at = self.count("the offset the window starts at")?;
        let at = usize::try_from(at)
            .map_err(|_| ScriptError::new("an offset may not be negative", at_span))?;
        Ok(Location { descent, at })
    }

    fn value(&mut self) -> Result<Val, ScriptError> {
        let span = self.span();
        match self.peek() {
            Some(Tok::Ident(_)) => {
                let (name, _) = self.ident("a word")?;
                // The one place a value reads two tokens: `untuple 2` is an
                // instruction, and an instruction that takes a count is still
                // one word to the reader.
                let count = match self.peek() {
                    Some(Tok::Int(n)) => {
                        let n = *n;
                        self.bump();
                        Some(n)
                    }
                    _ => None,
                };
                let end = self.toks[self.pos.saturating_sub(1)].span.1;
                Ok(Val::Word(name, count, (span.0, end)))
            }
            Some(Tok::Int(_)) | Some(Tok::Dash) => {
                let negative = self.peek() == Some(&Tok::Dash);
                if negative {
                    self.bump();
                }
                match self.peek() {
                    Some(Tok::Int(n)) => {
                        let n = if negative { -*n } else { *n };
                        let end = self.toks[self.pos].span.1;
                        self.bump();
                        Ok(Val::Int(n, (span.0, end)))
                    }
                    _ => Err(ScriptError::new("expected a number after '-'", self.span())),
                }
            }
            Some(Tok::Str(_)) => {
                let Some(Spanned {
                    tok: Tok::Str(text),
                    span,
                }) = self.bump()
                else {
                    unreachable!("peeked a string")
                };
                Ok(Val::Str(text.clone(), *span))
            }
            Some(Tok::LBrace) => {
                self.bump();
                let body = self.term()?;
                let end = self.expect(Tok::RBrace, "'}' or an instruction")?;
                Ok(Val::Term(body, (span.0, end.1)))
            }
            Some(Tok::LBracket) => {
                let (items, end) = self.items(Tok::RBracket, "']'")?;
                Ok(Val::List(items, (span.0, end.1)))
            }
            Some(Tok::LParen) => {
                let (items, end) = self.items(Tok::RParen, "')'")?;
                Ok(Val::Tuple(items, (span.0, end.1)))
            }
            Some(other) => Err(ScriptError::new(
                format!("expected a value, found {}", describe(other)),
                span,
            )),
            None => Err(ScriptError::new("expected a value", span)),
        }
    }

    /// A comma-separated run inside brackets or parentheses, trailing comma
    /// allowed — which is what makes `(1,)` a one-element tuple rather than a
    /// parenthesized `1`.
    fn items(&mut self, close: Tok, what: &str) -> Result<(Vec<Val>, Span), ScriptError> {
        self.bump();
        let mut items = Vec::new();
        while self.peek() != Some(&close) {
            items.push(self.value()?);
            if self.peek() == Some(&Tok::Comma) {
                self.bump();
                continue;
            }
            break;
        }
        let end = self.expect(close, what)?;
        Ok((items, end))
    }

    /// A run of instructions, up to but not including the closing brace.
    fn term(&mut self) -> Result<Vec<Node>, ScriptError> {
        let mut out = Vec::new();
        while !matches!(self.peek(), Some(&Tok::RBrace) | None) {
            out.push(self.instruction()?);
        }
        Ok(out)
    }

    fn instruction(&mut self) -> Result<Node, ScriptError> {
        let (word, span) = self.ident("an instruction")?;

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

        // `dip k { ... }` is a block written out; `dip k <sentence>` is a call
        // that hides `k` values. The ISA has one instruction for both — a body
        // it can see and a body it cannot — and the two spellings are that
        // difference.
        if word == "dip" {
            let depth = self.usize_count(&word, span)?;
            if self.peek() == Some(&Tok::LBrace) {
                return Ok(Node::Dip {
                    depth,
                    origins: Vec::new(),
                    body: self.block()?,
                });
            }
            return Ok(Node::Call {
                depth,
                target: self.sentence(span)?,
            });
        }

        if word == "jump" {
            return Ok(Node::Call {
                depth: 0,
                target: self.sentence(span)?,
            });
        }

        if word == "push" {
            let value = self.value()?;
            return Ok(Node::Op(Instruction::Push(literal(&value, self.prog)?)));
        }

        let inst = match word.as_str() {
            "pick" => Instruction::Pick(self.usize_count(&word, span)?),
            "roll" => Instruction::Roll(self.usize_count(&word, span)?),
            "tuple" => Instruction::Tuple(self.usize_count(&word, span)?),
            "untuple" => Instruction::Untuple(self.usize_count(&word, span)?),
            other => match plain_instruction(other) {
                Some(inst) => inst,
                None => {
                    return Err(ScriptError::new(
                        format!("'{}' is not an instruction a derivation may hold", other),
                        span,
                    )
                    .with_help(
                        "every instruction has a spelling; `--list-rules` \
                         describes the shape of a term",
                    ));
                }
            },
        };
        Ok(Node::Op(inst))
    }

    fn block(&mut self) -> Result<Vec<Node>, ScriptError> {
        self.expect(Tok::LBrace, "'{'")?;
        let body = self.term()?;
        self.expect(Tok::RBrace, "'}'")?;
        Ok(body)
    }

    fn usize_count(&mut self, word: &str, span: Span) -> Result<usize, ScriptError> {
        let at = self.span();
        match self.peek() {
            Some(Tok::Int(n)) => {
                let n = *n;
                self.bump();
                usize::try_from(n)
                    .map_err(|_| ScriptError::new(format!("`{}` needs a count", word), at))
            }
            _ => Err(ScriptError::new(format!("`{}` needs a number", word), span)
                .with_help(format!("for example `{} 0`", word))),
        }
    }

    /// The sentence a call names, resolved the way everything else resolves
    /// one: an exact name, an unambiguous trailing part of one, or an index.
    fn sentence(&mut self, span: Span) -> Result<SentenceIndex, ScriptError> {
        let at = self.span();
        let ident = match self.peek() {
            Some(Tok::Ident(name)) => {
                let name = name.clone();
                self.bump();
                name
            }
            Some(Tok::Int(n)) => {
                let name = n.to_string();
                self.bump();
                name
            }
            _ => {
                return Err(ScriptError::new("a call needs a sentence", span)
                    .with_help("a name, a unique trailing part of one, or an index"));
            }
        };
        resolve_sentence(self.prog.library(), &ident).map_err(|why| ScriptError::new(why, at))
    }

    /// The equation a step names, built from its arguments.
    fn kind(&self, mut f: Fields) -> Result<StepKind, ScriptError> {
        let prog = self.prog;
        let kind = match f.rule.as_str() {
            "collapse" => StepKind::Rule(Rule::Collapse {
                k: f.count("k")?,
                j: f.count("j")?,
                a: f.term("a")?,
                outer: Vec::new(),
                inner: Vec::new(),
            }),
            "elim_dip0" => StepKind::Rule(Rule::ElimDip0 {
                a: f.term("a")?,
                origins: Vec::new(),
            }),
            "interchange" => StepKind::Rule(Rule::Interchange {
                x: f.node("x")?,
                framed: f.node("framed")?,
                n: f.int("n")?,
                m: f.int("m")?,
            }),
            "fuse" => StepKind::Rule(Rule::Fuse {
                k: f.count("k")?,
                a: f.term("a")?,
                b: f.term("b")?,
                a_origins: Vec::new(),
                b_origins: Vec::new(),
            }),
            "hoist" => StepKind::Rule(Rule::Hoist {
                k: f.count("k")?,
                x: f.term("x")?,
                origins: Vec::new(),
                then_arm: f.term("then")?,
                else_arm: f.term("else")?,
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            }),
            "distribute" => StepKind::Rule(Rule::Distribute {
                then_arm: f.term("then")?,
                else_arm: f.term("else")?,
                suffix: f.term("suffix")?,
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            }),
            "fold_branch" => StepKind::Rule(Rule::FoldBranch {
                c: f.literal("c", prog)?,
                then_arm: f.term("then")?,
                else_arm: f.term("else")?,
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            }),
            "eval" => StepKind::Rule(Rule::Eval {
                op: f.op("op")?,
                inputs: f.literals("inputs", prog)?,
            }),
            "annihilate" => StepKind::Rule(Rule::Annihilate {
                x: f.term("x")?,
                n: f.count("n")?,
                m: f.count("m")?,
            }),
            "commute" => StepKind::Rule(Rule::Commute { op: f.op("op")? }),
            "split_bool" => StepKind::Rule(Rule::SplitBool),
            "counit" => StepKind::Rule(Rule::Counit { d: f.count("d")? }),
            "counit_under" => StepKind::Rule(Rule::CounitUnder),
            "retest" => StepKind::Rule(Rule::Retest {
                arm: f.arm("arm")?,
                inner: f.node("inner")?,
                rest: f.term("rest")?,
                other: f.term("other")?,
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            }),
            "specialize_equal" => StepKind::Rule(Rule::SpecializeEqual {
                c: f.literal("c", prog)?,
                then_arm: f.term("then")?,
                else_arm: f.term("else")?,
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            }),
            "copy_const" => StepKind::Rule(Rule::CopyConst {
                c: f.literal("c", prog)?,
            }),
            "copy_assoc" => StepKind::Rule(Rule::CopyAssoc { d: f.count("d")? }),
            "copy_nat" => StepKind::Rule(Rule::CopyNat {
                x: f.term("x")?,
                n: f.count("n")?,
                m: f.count("m")?,
            }),
            "bool_result" => StepKind::Rule(Rule::BoolResult { op: f.op("op")? }),
            "cancel_tuple" => StepKind::Rule(Rule::CancelTuple { n: f.count("n")? }),
            "roll_cycle" => StepKind::Rule(Rule::RollCycle { d: f.count("d")? }),
            "unframe" => StepKind::Rule(Rule::Unframe {
                framed: f.node("framed")?,
                n: f.count("n")?,
                m: f.count("m")?,
            }),
            "pick_roll" => StepKind::Rule(Rule::PickRoll { d: f.count("d")? }),
            "unfold" => StepKind::Unfold {
                depth: f.count("depth")?,
                target: f.sentence("target", prog)?,
            },
            other => {
                return Err(
                    ScriptError::new(format!("unknown equation '{}'", other), f.span)
                        .with_help(format!("equations: {}", equation_names().join(", "))),
                );
            }
        };
        f.finish()?;
        Ok(kind)
    }
}

/// The arguments a step was given, taken one at a time as the equation asks.
struct Fields {
    rule: String,
    span: Span,
    args: Vec<(String, Span, Val)>,
}

impl Fields {
    fn take(&mut self, name: &str) -> Result<Val, ScriptError> {
        match self.args.iter().position(|(n, _, _)| n == name) {
            Some(at) => Ok(self.args.remove(at).2),
            None => Err(
                ScriptError::new(format!("`{}` needs `{}`", self.rule, name), self.span).with_help(
                    match arg_names(&self.rule) {
                        Some([]) => format!("`{}` takes no arguments", self.rule),
                        Some(names) => format!("it takes {}", names.join(", ")),
                        None => "no such equation".to_string(),
                    },
                ),
            ),
        }
    }

    /// Nothing may be left over: an argument the equation does not read is
    /// either a typo or a step meant for a different one, and quietly ignoring
    /// it would let both through.
    fn finish(&self) -> Result<(), ScriptError> {
        let Some((name, span, _)) = self.args.first() else {
            return Ok(());
        };
        Err(ScriptError::new(
            format!("`{}` takes no argument `{}`", self.rule, name),
            *span,
        )
        .with_help(match arg_names(&self.rule) {
            Some([]) => format!("`{}` takes no arguments", self.rule),
            Some(names) => format!("it takes {}", names.join(", ")),
            None => "no such equation".to_string(),
        }))
    }

    fn int(&mut self, name: &str) -> Result<i64, ScriptError> {
        let val = self.take(name)?;
        match val {
            Val::Int(n, _) => Ok(n),
            other => Err(wanted(name, "a number", &other)),
        }
    }

    fn count(&mut self, name: &str) -> Result<usize, ScriptError> {
        let val = self.take(name)?;
        match val {
            Val::Int(n, span) => usize::try_from(n)
                .map_err(|_| ScriptError::new(format!("`{}` may not be negative", name), span)),
            other => Err(wanted(name, "a count", &other)),
        }
    }

    fn term(&mut self, name: &str) -> Result<Vec<Node>, ScriptError> {
        let val = self.take(name)?;
        match val {
            Val::Term(nodes, _) => Ok(nodes),
            other => Err(wanted(name, "a term, in braces", &other)),
        }
    }

    /// A term holding exactly one node. Several equations take a single node —
    /// the thing that moves in `interchange`, the branch `retest` collapses —
    /// and writing it as a term of one keeps the format to one spelling for
    /// program text.
    fn node(&mut self, name: &str) -> Result<Node, ScriptError> {
        let val = self.take(name)?;
        let span = val.span();
        match val {
            Val::Term(mut nodes, _) if nodes.len() == 1 => Ok(nodes.remove(0)),
            Val::Term(nodes, _) => Err(ScriptError::new(
                format!(
                    "`{}` is one node, and this term holds {}",
                    name,
                    nodes.len()
                ),
                span,
            )),
            other => Err(wanted(name, "a term holding one node", &other)),
        }
    }

    fn literal(&mut self, name: &str, prog: &Program) -> Result<Value, ScriptError> {
        let val = self.take(name)?;
        literal(&val, prog)
    }

    fn literals(&mut self, name: &str, prog: &Program) -> Result<Vec<Value>, ScriptError> {
        let val = self.take(name)?;
        match val {
            Val::List(items, _) => items.iter().map(|v| literal(v, prog)).collect(),
            other => Err(wanted(name, "a list of literals, in brackets", &other)),
        }
    }

    fn op(&mut self, name: &str) -> Result<Instruction, ScriptError> {
        let val = self.take(name)?;
        let span = val.span();
        let Val::Word(word, count, _) = &val else {
            return Err(wanted(name, "an instruction", &val));
        };
        let inst = match (word.as_str(), count) {
            ("pick", Some(n)) => Instruction::Pick(nonneg(*n, span)?),
            ("roll", Some(n)) => Instruction::Roll(nonneg(*n, span)?),
            ("tuple", Some(n)) => Instruction::Tuple(nonneg(*n, span)?),
            ("untuple", Some(n)) => Instruction::Untuple(nonneg(*n, span)?),
            (other, None) => match plain_instruction(other) {
                Some(inst) => inst,
                None => {
                    return Err(ScriptError::new(
                        format!("'{}' is not an instruction", other),
                        span,
                    ));
                }
            },
            (other, Some(_)) => {
                return Err(ScriptError::new(
                    format!("`{}` takes no count", other),
                    span,
                ));
            }
        };
        Ok(inst)
    }

    fn arm(&mut self, name: &str) -> Result<Arm, ScriptError> {
        let val = self.take(name)?;
        let span = val.span();
        match &val {
            Val::Word(word, None, _) if word == "then" => Ok(Arm::Then),
            Val::Word(word, None, _) if word == "else" => Ok(Arm::Else),
            _ => Err(
                ScriptError::new(format!("`{}` is `then` or `else`", name), span)
                    .with_help("which arm of the outer branch the law is being read at"),
            ),
        }
    }

    fn sentence(&mut self, name: &str, prog: &Program) -> Result<SentenceIndex, ScriptError> {
        let val = self.take(name)?;
        let span = val.span();
        let ident = match &val {
            Val::Word(word, None, _) => word.clone(),
            Val::Int(n, _) => n.to_string(),
            other => return Err(wanted(name, "the name of a sentence", other)),
        };
        resolve_sentence(prog.library(), &ident).map_err(|why| ScriptError::new(why, span))
    }
}

fn nonneg(n: i64, span: Span) -> Result<usize, ScriptError> {
    usize::try_from(n).map_err(|_| ScriptError::new("a count may not be negative", span))
}

fn wanted(name: &str, what: &str, got: &Val) -> ScriptError {
    ScriptError::new(
        format!("`{}` is {}, and this is {}", name, what, got.describe()),
        got.span(),
    )
}

/// A value, read as the literal it denotes.
///
/// A bare word is a **symbol**, looked up rather than built, because a symbol
/// compares by `id` and one made from its text would equal nothing in the
/// program. `true` and `false` are the two words that are not, since they are
/// the only literals the language spells with letters.
fn literal(val: &Val, prog: &Program) -> Result<Value, ScriptError> {
    Ok(match val {
        Val::Int(n, _) => Value::Int(*n),
        Val::Str(text, _) => Value::ConstString(text.clone()),
        Val::Word(word, None, _) if word == "true" => Value::Bool(true),
        Val::Word(word, None, _) if word == "false" => Value::Bool(false),
        Val::Word(word, None, span) => {
            resolve_symbol(prog.library(), word).map_err(|why| ScriptError::new(why, *span))?
        }
        Val::Tuple(items, _) => Value::Tuple(
            items
                .iter()
                .map(|v| literal(v, prog))
                .collect::<Result<_, _>>()?,
        ),
        other => {
            return Err(ScriptError::new(
                format!("expected a literal, found {}", other.describe()),
                other.span(),
            )
            .with_help(
                "an integer, `true`/`false`, a `\"const string\"`, a \
                 symbol by name, or a `(tuple, of, them)`",
            ));
        }
    })
}

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Ident(name) => format!("'{}'", name),
        Tok::Int(n) => format!("'{}'", n),
        Tok::Str(text) => format!("string literal \"{}\"", text),
        Tok::Arrow(Direction::Forward) => "'->'".to_string(),
        Tok::Arrow(Direction::Reverse) => "'<-'".to_string(),
        Tok::Dash => "'-'".to_string(),
        Tok::At => "'@'".to_string(),
        Tok::Dot => "'.'".to_string(),
        Tok::Comma => "','".to_string(),
        Tok::Semi => "';'".to_string(),
        Tok::Eq => "'='".to_string(),
        Tok::LParen => "'('".to_string(),
        Tok::RParen => "')'".to_string(),
        Tok::LBrace => "'{'".to_string(),
        Tok::RBrace => "'}'".to_string(),
        Tok::LBracket => "'['".to_string(),
        Tok::RBracket => "']'".to_string(),
    }
}

/// Every step kind, and the arguments it takes.
///
/// What an error message reads to say what an equation wanted. The writer keeps
/// its own list — it has to, since it writes the values too — and the two are
/// held together by `every_equation_survives_the_round_trip` rather than by
/// eye: a name written but not expected comes back as "takes no argument".
pub(crate) fn arg_names(rule: &str) -> Option<&'static [&'static str]> {
    Some(match rule {
        "collapse" => &["k", "j", "a"],
        "elim_dip0" => &["a"],
        "interchange" => &["x", "framed", "n", "m"],
        "fuse" => &["k", "a", "b"],
        "hoist" => &["k", "x", "then", "else"],
        "distribute" => &["then", "else", "suffix"],
        "fold_branch" => &["c", "then", "else"],
        "eval" => &["op", "inputs"],
        "annihilate" => &["x", "n", "m"],
        "commute" => &["op"],
        "split_bool" => &[],
        "counit" => &["d"],
        "counit_under" => &[],
        "retest" => &["arm", "inner", "rest", "other"],
        "copy_const" => &["c"],
        "copy_assoc" => &["d"],
        "copy_nat" => &["x", "n", "m"],
        "bool_result" => &["op"],
        "cancel_tuple" => &["n"],
        "roll_cycle" => &["d"],
        "unframe" => &["framed", "n", "m"],
        "pick_roll" => &["d"],
        "unfold" => &["depth", "target"],
        _ => return None,
    })
}

/// The step kinds, in the order the equation table in `docs/tactics.md` lists
/// them. `unfold` is last because it is not an equation of the calculus.
pub(crate) fn equation_names() -> Vec<&'static str> {
    vec![
        "collapse",
        "elim_dip0",
        "interchange",
        "fuse",
        "hoist",
        "distribute",
        "fold_branch",
        "eval",
        "annihilate",
        "commute",
        "split_bool",
        "counit",
        "counit_under",
        "retest",
        "specialize_equal",
        "copy_const",
        "copy_assoc",
        "copy_nat",
        "bool_result",
        "cancel_tuple",
        "roll_cycle",
        "unframe",
        "pick_roll",
        "unfold",
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::{Library, assemble};

    fn program_of(code: &str) -> &'static Program<'static> {
        let library = assemble(code).unwrap_or_else(|e| panic!("{:?}", e));
        Box::leak(Box::new(Program::new(Box::leak(Box::new(library)))))
    }

    fn empty() -> &'static Program<'static> {
        Box::leak(Box::new(Program::new(Box::leak(Box::new(Library::new())))))
    }

    /// Parse what was written, write what was parsed: the two have to be
    /// inverse or a file means something other than the run it records.
    fn round_trip(prog: &Program, steps: &[Step]) -> Vec<Step> {
        let text = write(prog, &[("x", steps)]).unwrap_or_else(|e| panic!("{}", e));
        let parsed = parse(&text, prog).unwrap_or_else(|e| panic!("{}", e.render(&text)));
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].identity, "x");
        parsed[0].steps.clone()
    }

    fn op(i: Instruction) -> Node {
        Node::Op(i)
    }

    fn step(kind: StepKind, dir: Direction, loc: Location) -> Step {
        Step { kind, dir, loc }
    }

    #[test]
    fn a_step_survives_being_written_and_read() {
        let steps = vec![step(
            StepKind::Rule(Rule::Annihilate {
                x: vec![op(Instruction::Add)],
                n: 2,
                m: 2,
            }),
            Direction::Forward,
            Location::root(3),
        )];
        assert_eq!(round_trip(empty(), &steps), steps);
    }

    #[test]
    fn a_location_survives_with_its_whole_descent() {
        let steps = vec![step(
            StepKind::Rule(Rule::SplitBool),
            Direction::Reverse,
            Location {
                descent: vec![
                    (3, Selector::Then),
                    (0, Selector::Body),
                    (1, Selector::Else),
                ],
                at: 2,
            },
        )];
        assert_eq!(round_trip(empty(), &steps), steps);
    }

    /// Every equation, so that adding one without a spelling is a failing test
    /// rather than a file that cannot be written.
    #[test]
    fn every_equation_survives_the_round_trip() {
        let branch = Node::Branch {
            then_origin: TERM_ORIGIN.to_string(),
            then_body: vec![op(Instruction::Add)],
            else_origin: TERM_ORIGIN.to_string(),
            else_body: Vec::new(),
        };
        let rules = vec![
            Rule::Collapse {
                k: 2,
                j: 3,
                a: vec![op(Instruction::Add)],
                outer: Vec::new(),
                inner: Vec::new(),
            },
            Rule::ElimDip0 {
                a: vec![op(Instruction::Drop)],
                origins: Vec::new(),
            },
            Rule::Interchange {
                x: op(Instruction::Add),
                framed: Node::Dip {
                    depth: 2,
                    origins: Vec::new(),
                    body: vec![op(Instruction::Drop)],
                },
                n: 2,
                m: 2,
            },
            Rule::Fuse {
                k: 1,
                a: vec![op(Instruction::Add)],
                b: vec![op(Instruction::Drop)],
                a_origins: Vec::new(),
                b_origins: Vec::new(),
            },
            Rule::Hoist {
                k: 1,
                x: vec![op(Instruction::Drop)],
                origins: Vec::new(),
                then_arm: vec![op(Instruction::Add)],
                else_arm: Vec::new(),
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            },
            Rule::Distribute {
                then_arm: vec![op(Instruction::Add)],
                else_arm: Vec::new(),
                suffix: vec![op(Instruction::Drop)],
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            },
            Rule::FoldBranch {
                c: Value::Bool(true),
                then_arm: vec![op(Instruction::Add)],
                else_arm: Vec::new(),
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            },
            Rule::Eval {
                op: Instruction::Equal,
                inputs: vec![Value::Int(1), Value::Int(2)],
            },
            Rule::Annihilate {
                x: vec![op(Instruction::Add)],
                n: 2,
                m: 2,
            },
            Rule::Commute {
                op: Instruction::Add,
            },
            Rule::SplitBool,
            Rule::Counit { d: 4 },
            Rule::CounitUnder,
            Rule::Retest {
                arm: Arm::Else,
                inner: branch.clone(),
                rest: vec![op(Instruction::Drop)],
                other: Vec::new(),
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            },
            Rule::CopyConst { c: Value::Int(9) },
            Rule::CopyAssoc { d: 2 },
            Rule::CopyNat {
                x: vec![op(Instruction::Add)],
                n: 2,
                m: 2,
            },
            Rule::BoolResult {
                op: Instruction::IsBool,
            },
            Rule::CancelTuple { n: 3 },
            Rule::RollCycle { d: 2 },
            Rule::Unframe {
                framed: Node::Dip {
                    depth: 2,
                    origins: Vec::new(),
                    body: vec![op(Instruction::Add)],
                },
                n: 2,
                m: 2,
            },
            Rule::PickRoll { d: 3 },
            Rule::SpecializeEqual {
                c: Value::Int(9),
                then_arm: vec![op(Instruction::Not)],
                else_arm: vec![op(Instruction::IsBool)],
                then_origin: TERM_ORIGIN.to_string(),
                else_origin: TERM_ORIGIN.to_string(),
            },
        ];
        // Every name in the table is covered, so a new equation shows up here
        // as a missing case rather than as a file nobody can write.
        let mut named: Vec<&str> = rules.iter().map(|r| r.name()).collect();
        named.push("unfold");
        let mut all = equation_names();
        named.sort();
        all.sort();
        assert_eq!(named, all, "an equation has no round-trip test");

        let steps: Vec<Step> = rules
            .into_iter()
            .map(|r| step(StepKind::Rule(r), Direction::Forward, Location::root(0)))
            .collect();
        assert_eq!(round_trip(empty(), &steps), steps);
    }

    /// A sentence rides as a name, so the file says the same thing to a corpus
    /// that assembled its sentences in another order.
    #[test]
    fn a_call_is_written_by_name() {
        let prog = program_of("sentence f { drop 0 }\nsentence probe { jump f }");
        let target = resolve_sentence(prog.library(), "f").unwrap();
        let steps = vec![
            step(
                StepKind::Unfold { depth: 0, target },
                Direction::Forward,
                Location::root(0),
            ),
            step(
                StepKind::Rule(Rule::Interchange {
                    x: op(Instruction::Add),
                    framed: Node::Call { depth: 2, target },
                    n: 2,
                    m: 2,
                }),
                Direction::Reverse,
                Location::root(1),
            ),
        ];
        let text = write(prog, &[("x", &steps)]).unwrap();
        assert!(text.contains("target = f"), "{}", text);
        assert!(text.contains("dip 2 f"), "{}", text);
        assert_eq!(round_trip(prog, &steps), steps);
    }

    #[test]
    fn every_shape_of_literal_survives() {
        let prog = program_of("symbol s\nsentence probe { push s drop 0 }");
        let sym = resolve_symbol(prog.library(), "s").unwrap();
        for value in [
            Value::Int(-3),
            Value::Bool(false),
            Value::ConstString("hi there".to_string()),
            sym.clone(),
            Value::unit(),
            Value::Tuple(vec![Value::Int(1)]),
            Value::Tuple(vec![Value::Int(1), sym]),
        ] {
            let steps = vec![step(
                StepKind::Rule(Rule::CopyConst { c: value.clone() }),
                Direction::Forward,
                Location::root(0),
            )];
            assert_eq!(round_trip(prog, &steps), steps, "{:?}", value);
        }
    }

    fn err(source: &str) -> String {
        let e = parse(source, empty())
            .err()
            .unwrap_or_else(|| panic!("`{}` unexpectedly parsed", source));
        format!(
            "{}{}",
            e.message,
            e.help.map(|h| format!(" | {}", h)).unwrap_or_default()
        )
    }

    #[test]
    fn a_file_in_another_format_version_is_refused() {
        let msg = err("derivation 2;\n");
        assert!(msg.contains("derivation format 2"), "{}", msg);
        assert!(msg.contains("reads format 1"), "{}", msg);
    }

    #[test]
    fn a_missing_argument_says_which_and_what_the_equation_takes() {
        let msg = err("derivation 1; proof x { annihilate(x = { add }, n = 2) -> @0; }");
        assert!(msg.contains("`annihilate` needs `m`"), "{}", msg);
        assert!(msg.contains("x, n, m"), "{}", msg);
    }

    #[test]
    fn an_argument_the_equation_does_not_read_is_refused() {
        let msg = err("derivation 1; proof x { counit(d = 0, k = 1) -> @0; }");
        assert!(msg.contains("takes no argument `k`"), "{}", msg);
    }

    #[test]
    fn an_argument_of_the_wrong_shape_says_what_was_wanted() {
        let msg = err("derivation 1; proof x { counit(d = { add }) -> @0; }");
        assert!(msg.contains("`d` is a count"), "{}", msg);
        assert!(msg.contains("a term"), "{}", msg);
    }

    #[test]
    fn an_unknown_equation_lists_the_real_ones() {
        let msg = err("derivation 1; proof x { annihilat(x = { add }) -> @0; }");
        assert!(msg.contains("unknown equation 'annihilat'"), "{}", msg);
        assert!(msg.contains("annihilate"), "{}", msg);
    }

    #[test]
    fn a_step_with_no_direction_says_what_a_direction_is_for() {
        let msg = err("derivation 1; proof x { split_bool @0; }");
        assert!(msg.contains("expected `->` or `<-`"), "{}", msg);
    }

    #[test]
    fn a_word_that_is_not_an_instruction_says_so() {
        let msg = err("derivation 1; proof x { elim_dip0(a = { assert }) -> @0; }");
        assert!(msg.contains("'assert' is not an instruction"), "{}", msg);
        assert!(msg.contains("every instruction has a spelling"), "{}", msg);
    }

    #[test]
    fn a_node_argument_holding_two_nodes_is_refused() {
        let msg = err(
            "derivation 1; proof x { retest(arm = then, inner = { add drop }, rest = { }, other = { }) -> @0; }",
        );
        assert!(msg.contains("`inner` is one node"), "{}", msg);
    }

    #[test]
    fn spans_point_at_the_offending_word() {
        let src = "derivation 1; proof x { counit(d = 0) -> [0.thn] @0; }";
        let e = parse(src, empty()).unwrap_err();
        assert_eq!(&src[e.span.0..e.span.1], "thn");
    }

    #[test]
    fn comments_are_skipped() {
        let src = "// a note\nderivation 1;\n\n// another\nproof x { split_bool -> @0; }\n";
        assert_eq!(parse(src, empty()).unwrap().len(), 1);
    }

    #[test]
    fn a_file_may_hold_several_proofs() {
        let src = "derivation 1; proof a { split_bool -> @0; } proof b { counit(d = 1) <- @2; }";
        let out = parse(src, empty()).unwrap();
        assert_eq!(out.len(), 2);
        assert_eq!(out[0].identity, "a");
        assert_eq!(out[1].steps[0].dir, Direction::Reverse);
        assert_eq!(out[1].steps[0].loc, Location::root(2));
    }

    /// A derivation of nothing is a derivation: an identity whose two sides are
    /// already the same term is proved by no steps at all.
    #[test]
    fn a_proof_may_hold_no_steps() {
        let out = parse("derivation 1; proof a { }", empty()).unwrap();
        assert!(out[0].steps.is_empty());
    }
}
