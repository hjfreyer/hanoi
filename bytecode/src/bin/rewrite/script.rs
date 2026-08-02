//! The tactic script language: tokenizer, parser, and name resolution.
//!
//! ```text
//! script := def*
//! def    := "tactic" ident "=" expr ";"
//! expr   := choice
//! choice := seq ("|" seq)*
//! seq    := prim (";" prim)*
//! prim   := ident | ident "(" args ")" | "(" expr ")"
//! ```
//!
//! Two precedence levels, one more than the rest of the codebase has. Hand
//! written recursive descent, per house style — a parser generator was tried
//! twice in this repo and abandoned both times.
//!
//! Unlike the `.hana` tokenizer, every token here carries a byte span, so an
//! error can point at the offending word instead of describing it. That is
//! deliberate: the failure mode worth avoiding is the one the composer
//! templates have, where a message names text the user never wrote.

use std::collections::{HashMap, HashSet};

use crate::rules::{rule_by_name, Rule, ALL_RULES};
use crate::tactic::Tactic;

/// Reproduces what the old `--dip-normalize`, `--factor-branches` and
/// `--annihilate` flags did, as named tactics that can be recombined.
pub(crate) const PRELUDE: &str = r#"
// Splice every call into its caller, all the way down, leaving one flat
// sentence. `each` alone already expands a whole sequence transitively, since
// a spliced body is rescanned where it landed; the `bu` is what reaches into
// branch arms as well.
//
// For less than all of it, `once(inline)` takes the first call only, and
// `repeat_n(k, once(inline))` takes k of them.
tactic inline_all = repeat(bu(each(inline)));

// Nothing is expanded unless you ask. The listing names every call on one
// line, and you inline the ones you care about.
tactic default = id;

// Move dips left, fuse the ones that meet, and keep nested dips collapsed so
// the interchange rule sees a dip's true hidden depth.
tactic dips = repeat(bu(try(each(collapse)); try(each(sink)); try(each(fuse))));

// Split every dip into a nest of unary `dip 1`s. Presentation only, and the
// exact inverse of `collapse` — never put both in one `repeat`.
tactic unary = repeat(bu(each(expand)));

tactic factoring  = repeat(bu(each(factor_branch)));
tactic annihilate = repeat(bu(each(annihilate_drop)));

// Throw away work that does nothing. `pick_drop_to_roll` leaves a `roll 0`
// behind when d is 0, and `annihilate_drop` can empty a dip body; `noop`
// clears up after both, which is why these three belong together.
tactic cleanup = repeat(bu(each(annihilate_drop, pick_drop_to_roll, noop,
                                fold_branch)));

// Push what follows a branch into both of its arms, so a rule that only holds
// on one side can see it. Kept out of `all` and `cleanup`: it duplicates code
// on purpose, which is the opposite of what those two are for.
tactic distribute = repeat(bu(each(distribute_branch)));

// Splice plain calls into their call sites. This is what lets the other rules
// reach across a frame: a branch one level down and the instruction after the
// call are not in the same sequence until the frame is gone. It discards the
// origin labels, so it is opt-in rather than part of `all`.
tactic flatten = repeat(bu(each(flatten_call)));

// Everything at once, which is what passing all three flags used to mean.
tactic all = repeat(bu(try(each(annihilate_drop, pick_drop_to_roll, noop,
                                fold_branch));
                       try(each(factor_branch));
                       try(each(collapse)); try(each(sink)); try(each(fuse))));

// What `--dip-normalize` was.
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
    fn new(message: impl Into<String>, span: Span) -> Self {
        ScriptError {
            message: message.into(),
            span,
            help: None,
        }
    }

    fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Renders the error against the source, pointing at the span.
    pub(crate) fn render(&self, source: &str) -> String {
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
        out.push_str(&format!(" --> tactic:{}:{}\n", line_no, column + 1));
        out.push_str(&format!("  | {}\n", &source[line_start..line_end]));
        out.push_str(&format!("  | {}{}\n", " ".repeat(column), "^".repeat(width)));
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
    Tactic,
    Eq,
    Semi,
    Comma,
    Pipe,
    LParen,
    RParen,
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
                while i < bytes.len() && {
                    let c = bytes[i] as char;
                    c.is_alphanumeric() || c == '_'
                } {
                    i += 1;
                }
                match &src[start..i] {
                    "tactic" => Tok::Tactic,
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
enum Expr {
    Name(String, Span),
    Call(String, Span, Vec<Arg>),
    Seq(Vec<Expr>),
    Choice(Vec<Expr>),
}

enum Arg {
    Expr(Expr),
    Int(usize),
}

struct Parser<'a> {
    toks: &'a [Spanned],
    pos: usize,
    end: usize,
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
            if !matches!(self.toks.get(self.pos + 1).map(|s| &s.tok), Some(Tok::Ident(_)) | Some(Tok::LParen))
            {
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
        Ok(Arg::Expr(self.expr()?))
    }
}

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Ident(name) => format!("'{}'", name),
        Tok::Int(n) => format!("'{}'", n),
        Tok::Tactic => "'tactic'".to_string(),
        Tok::Eq => "'='".to_string(),
        Tok::Semi => "';'".to_string(),
        Tok::Comma => "','".to_string(),
        Tok::Pipe => "'|'".to_string(),
        Tok::LParen => "'('".to_string(),
        Tok::RParen => "')'".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Definitions and resolution
// ---------------------------------------------------------------------------

/// A set of named tactics, built from the prelude plus any user script.
pub(crate) struct Definitions {
    defs: HashMap<String, Expr>,
    /// Declaration order, for `--list-tactics`.
    order: Vec<String>,
}

impl Definitions {
    pub(crate) fn new() -> Self {
        Definitions {
            defs: HashMap::new(),
            order: Vec::new(),
        }
    }

    /// Parses `tactic NAME = expr;` definitions, later ones shadowing earlier.
    pub(crate) fn load(&mut self, source: &str) -> Result<(), ScriptError> {
        let toks = tokenize(source)?;
        let mut p = Parser {
            toks: &toks,
            pos: 0,
            end: source.len(),
        };

        while p.peek().is_some() {
            p.expect(Tok::Tactic, "'tactic'")?;
            let name_span = p.span();
            let name = match p.bump() {
                Some(Spanned {
                    tok: Tok::Ident(name),
                    ..
                }) => name.clone(),
                _ => {
                    return Err(ScriptError::new("expected a tactic name", name_span));
                }
            };
            if rule_by_name(&name).is_some() {
                return Err(ScriptError::new(
                    format!("'{}' is a rule name", name),
                    name_span,
                )
                .with_help("rules and tactics are separate namespaces; pick another name"));
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

    /// Parses and resolves a single expression against these definitions.
    pub(crate) fn compile(&self, source: &str) -> Result<Tactic, ScriptError> {
        let toks = tokenize(source)?;
        let mut p = Parser {
            toks: &toks,
            pos: 0,
            end: source.len(),
        };
        let expr = p.expr()?;
        if let Some(tok) = p.peek() {
            return Err(ScriptError::new(
                format!("unexpected {} after the tactic", describe(tok)),
                p.span(),
            ));
        }
        self.resolve(&expr, &mut HashSet::new())
    }

    fn resolve(&self, expr: &Expr, visiting: &mut HashSet<String>) -> Result<Tactic, ScriptError> {
        match expr {
            Expr::Seq(parts) => Ok(Tactic::Seq(
                parts
                    .iter()
                    .map(|e| self.resolve(e, visiting))
                    .collect::<Result<_, _>>()?,
            )),
            Expr::Choice(parts) => Ok(Tactic::Choice(
                parts
                    .iter()
                    .map(|e| self.resolve(e, visiting))
                    .collect::<Result<_, _>>()?,
            )),
            Expr::Name(name, span) => self.resolve_name(name, *span, visiting),
            Expr::Call(name, span, args) => self.resolve_call(name, *span, args, visiting),
        }
    }

    fn resolve_name(
        &self,
        name: &str,
        span: Span,
        visiting: &mut HashSet<String>,
    ) -> Result<Tactic, ScriptError> {
        match name {
            "id" => return Ok(Tactic::Id),
            "fail" => return Ok(Tactic::Fail),
            _ => {}
        }

        if rule_by_name(name).is_some() {
            return Err(ScriptError::new(
                format!("'{}' is a rule, not a tactic", name),
                span,
            )
            .with_help(format!(
                "a rule has to be placed somewhere: write `each({})` to apply it \
                 everywhere in a sequence, or `once({})` for the first match",
                name, name
            )));
        }

        if COMBINATORS.iter().any(|(n, _)| *n == name) {
            return Err(
                ScriptError::new(format!("'{}' needs arguments", name), span).with_help(format!(
                    "write `{}(...)`",
                    name
                )),
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
            return Err(
                ScriptError::new(format!("tactic '{}' is defined in terms of itself", name), span)
                    .with_help(
                        "tactic definitions may not recurse, so that `repeat` is the only \
                         unbounded construct in the language",
                    ),
            );
        }
        let out = self.resolve(body, visiting);
        visiting.remove(name);
        out
    }

    fn resolve_call(
        &self,
        name: &str,
        span: Span,
        args: &[Arg],
        visiting: &mut HashSet<String>,
    ) -> Result<Tactic, ScriptError> {
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
            Shape::Rules => {
                if args.is_empty() {
                    return Err(ScriptError::new(
                        format!("`{}` needs at least one rule", name),
                        span,
                    ));
                }
                let mut rules: Vec<&'static dyn Rule> = Vec::new();
                for arg in args {
                    let Arg::Expr(Expr::Name(rule_name, rule_span)) = arg else {
                        return Err(ScriptError::new(
                            format!("`{}` takes rule names, not tactics", name),
                            span,
                        )
                        .with_help(format!("rules: {}", rule_names().join(", "))));
                    };
                    let Some(rule) = rule_by_name(rule_name) else {
                        return Err(ScriptError::new(
                            format!("unknown rule '{}'", rule_name),
                            *rule_span,
                        )
                        .with_help(format!("rules: {}", rule_names().join(", "))));
                    };
                    rules.push(rule);
                }
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
                let inner = Box::new(self.resolve(inner, visiting)?);
                Ok(match name {
                    "try" => Tactic::Try(inner),
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
                    Box::new(self.resolve(inner, visiting)?),
                ))
            }
        }
    }
}

enum Shape {
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

const COMBINATORS: &[(&str, Shape)] = &[
    ("each", Shape::Rules),
    ("once", Shape::Rules),
    ("try", Shape::One),
    ("repeat", Shape::One),
    ("children", Shape::One),
    ("bu", Shape::One),
    ("td", Shape::One),
    ("repeat_n", Shape::CountAndOne),
];

pub(crate) fn rule_names() -> Vec<&'static str> {
    ALL_RULES.iter().map(|r| r.name()).collect()
}

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
        format!("{}{}", e.message, e.help.map(|h| format!(" | {}", h)).unwrap_or_default())
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
        assert!(d
            .compile("a")
            .unwrap_err()
            .message
            .contains("defined in terms of itself"));
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
}
