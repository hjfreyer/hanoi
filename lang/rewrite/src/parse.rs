//! The term language, read back.
//!
//! [`Context`](crate::kernel::term::Context) writes a term; this reads one. The two
//! are inverses, deliberately: a `via` waypoint is a term the author writes
//! by hand, and it is written in the language the model prints rather than
//! in Hana's. A proof used to say `pick 0 push t1 equal` where the term
//! model said `copy(1) ; id(1) * push t1 ; equal`, and translating between
//! the two by hand was work the author should never have been doing.
//!
//! ```text
//! via { copy(1) ; id(1) * push types_test::t1 ; equal ; branch { … } { … } }
//! ```
//!
//! Nothing here pads. The term language says what it means — an implicit
//! passing-through is written `id(k) * A` — so a body whose halves do not meet
//! is a mistake with a name (`cannot compose 1 -> 2 with 1 -> 1`) rather than
//! something quietly widened into a shape the author did not ask for. That is
//! the difference from a Hana sentence, where padding is inferred, and it is
//! why the two spellings of one waypoint are not the same length.
//!
//! What a body may name comes from the [`Scope`]: sentences and symbols out
//! of the library.

use bytecode::{Library, SentenceIndex, Value};

use crate::kernel::term::{Context, Prim, TermIndex};

/// What names a body may use: the library it is written against.
pub struct Scope<'l> {
    pub library: &'l Library,
}

impl<'l> Scope<'l> {
    pub fn new(library: &'l Library) -> Self {
        Scope { library }
    }
}

/// Reads a term out of the language a [`Context`]'s printing writes, building
/// it in `ctx`.
pub fn parse_term(ctx: &mut Context, text: &str, scope: &Scope) -> Result<TermIndex, String> {
    let (term, rest) = compose(ctx, text, scope)?;
    let rest = rest.trim();
    if !rest.is_empty() {
        return Err(format!("unexpected {}", head_of(rest)));
    }
    Ok(term)
}

/// `a ; b ; c`, left-associated — so a right-nested compose keeps the
/// parentheses that printed it.
fn compose<'t>(
    ctx: &mut Context,
    text: &'t str,
    scope: &Scope,
) -> Result<(TermIndex, &'t str), String> {
    let (mut term, mut rest) = par(ctx, text, scope)?;
    while let Some(after) = rest.trim_start().strip_prefix(';') {
        let (next, tail) = par(ctx, after, scope)?;
        term = ctx.compose(term, next).map_err(|e| e.to_string())?;
        rest = tail;
    }
    Ok((term, rest))
}

/// `a * b * c`, left-associated, binding tighter than `;`.
fn par<'t>(
    ctx: &mut Context,
    text: &'t str,
    scope: &Scope,
) -> Result<(TermIndex, &'t str), String> {
    let (mut term, mut rest) = atom(ctx, text, scope)?;
    while let Some(after) = rest.trim_start().strip_prefix('*') {
        let (next, tail) = atom(ctx, after, scope)?;
        term = ctx.par(term, next);
        rest = tail;
    }
    Ok((term, rest))
}

fn atom<'t>(
    ctx: &mut Context,
    text: &'t str,
    scope: &Scope,
) -> Result<(TermIndex, &'t str), String> {
    let text = text.trim_start();
    if let Some(after) = text.strip_prefix('(') {
        let (term, rest) = compose(ctx, after, scope)?;
        let rest = rest
            .trim_start()
            .strip_prefix(')')
            .ok_or_else(|| format!("expected `)`, found {}", head_of(rest)))?;
        return Ok((term, rest));
    }
    let (head, rest) = word(text);
    match head {
        "" => Err(format!("expected a term, found {}", head_of(text))),
        "id" | "drop" | "copy" => {
            let (n, rest) = width(rest, head)?;
            Ok((
                match head {
                    "id" => ctx.id(n),
                    "drop" => ctx.drop(n),
                    _ => ctx.copy(n),
                },
                rest,
            ))
        }
        "branch" => {
            let (if_true, rest) = arm(ctx, rest, scope)?;
            let (if_false, rest) = arm(ctx, rest, scope)?;
            Ok((
                ctx.branch(if_true, if_false).map_err(|e| e.to_string())?,
                rest,
            ))
        }
        "call" => {
            let (path, rest) = word(rest.trim_start());
            let target = sentence_named(scope.library, path)?;
            let arity = crate::kernel::term::call_arity(scope.library, target)
                .map_err(|e| e.to_string())?;
            Ok((ctx.call(target, arity), rest))
        }
        "push" => {
            let (value, rest) = literal(rest, scope)?;
            Ok((ctx.op(Prim::Push(value)), rest))
        }
        mnemonic => {
            // Everything else is an instruction, spelled the way the machine
            // spells it. The three that carry a width read theirs here; the
            // rest are looked up by name, so this table cannot drift from the
            // instruction set the way a second list of names would.
            if let Some(build) = width_carrying(mnemonic) {
                let (n, rest) = number(rest.trim_start())
                    .ok_or_else(|| format!("`{}` wants a width", mnemonic))?;
                return Ok((ctx.op(build(n)), rest));
            }
            let prim = Prim::all()
                .into_iter()
                .find(|p| p.to_string() == mnemonic)
                .ok_or_else(|| match mnemonic {
                    "dip" => "a frame is a `*` against `id(n)`, not a `dip`".to_string(),
                    "jump" => "a call is `call name`".to_string(),
                    other => format!("no term is called `{}`", other),
                })?;
            Ok((ctx.op(prim), rest))
        }
    }
}

/// One brace-delimited branch arm.
fn arm<'t>(
    ctx: &mut Context,
    text: &'t str,
    scope: &Scope,
) -> Result<(TermIndex, &'t str), String> {
    let text = text
        .trim_start()
        .strip_prefix('{')
        .ok_or_else(|| format!("expected a branch arm in braces, found {}", head_of(text)))?;
    let (term, rest) = compose(ctx, text, scope)?;
    let rest = rest
        .trim_start()
        .strip_prefix('}')
        .ok_or_else(|| format!("expected `}}`, found {}", head_of(rest)))?;
    Ok((term, rest))
}

/// The `(n)` of a block leaf. Spelled with parentheses because that is how it
/// prints, and because `drop` alone is the instruction the model does not have.
fn width<'t>(text: &'t str, leaf: &str) -> Result<(usize, &'t str), String> {
    let text = text
        .trim_start()
        .strip_prefix('(')
        .ok_or_else(|| format!("`{}` is a block of some width: write `{}(1)`", leaf, leaf))?;
    let (n, rest) = number(text.trim_start()).ok_or_else(|| format!("`{}` wants a width", leaf))?;
    let rest = rest
        .trim_start()
        .strip_prefix(')')
        .ok_or_else(|| format!("expected `)` after the width of `{}`", leaf))?;
    Ok((n, rest))
}

/// A pushed value, in the spelling [`Value`]'s printing gives it.
fn literal<'t>(text: &'t str, scope: &Scope) -> Result<(Value, &'t str), String> {
    let text = text.trim_start();
    if let Some(after) = text.strip_prefix('"') {
        let end = after
            .find('"')
            .ok_or("a const string that never closes its quote")?;
        return Ok((
            Value::ConstString(after[..end].to_string()),
            &after[end + 1..],
        ));
    }
    if let Some(after) = text.strip_prefix('(') {
        // A tuple, in stack order — and `()` is the unit the untupling
        // instructions hand back.
        let mut rest = after.trim_start();
        let mut elements = Vec::new();
        while !rest.starts_with(')') {
            let (element, tail) = literal(rest, scope)?;
            elements.push(element);
            rest = tail.trim_start();
            rest = rest.strip_prefix(',').unwrap_or(rest).trim_start();
        }
        return Ok((Value::Tuple(elements), &rest[1..]));
    }
    if let Some((n, rest)) = signed(text) {
        return Ok((Value::Int(n), rest));
    }
    let (head, rest) = word(text);
    match head {
        "" => Err(format!("expected a value, found {}", head_of(text))),
        "true" => Ok((Value::Bool(true), rest)),
        "false" => Ok((Value::Bool(false), rest)),
        // Anything else names a symbol, which is exactly what a symbol is:
        // where it was declared, printed as the path the library keys it under.
        path => {
            let named = unique_name("symbol", path, scope.library.symbols.keys())?;
            Ok((scope.library.symbols[&named].clone(), rest))
        }
    }
}

fn width_carrying(mnemonic: &str) -> Option<fn(usize) -> Prim> {
    match mnemonic {
        "tuple" => Some(Prim::Tuple),
        "untuple" => Some(Prim::Untuple),
        "as_tuple" => Some(Prim::AsTuple),
        _ => None,
    }
}

/// A sentence by the name the library keys it under, or by an unambiguous
/// trailing part of one. Shared with the loader, which resolves an
/// `inline(name)` label the same way a `call name` resolves.
pub fn sentence_named(library: &Library, path: &str) -> Result<SentenceIndex, String> {
    if path.is_empty() {
        return Err("`call` wants the name of a sentence".to_string());
    }
    let named = unique_name("sentence", path, library.names.iter())?;
    Ok(library
        .names
        .iter_enumerated()
        .find(|(_, name)| **name == named)
        .map(|(idx, _)| idx)
        .expect("the name came out of this table"))
}

/// The one name in `names` that `path` picks out: itself, or the unambiguous
/// one it is a trailing part of — the reading an `identity` and a `jump`
/// already get, so a waypoint need not spell a whole path either.
fn unique_name<'n>(
    kind: &str,
    path: &str,
    names: impl Iterator<Item = &'n String>,
) -> Result<String, String> {
    let suffix = format!("::{}", path);
    let mut matches: Vec<&String> = names
        .filter(|name| *name == path || name.ends_with(&suffix))
        .collect();
    matches.sort();
    matches.dedup();
    match matches[..] {
        [one] => Ok(one.clone()),
        [] => Err(format!("no {} is called `{}`", kind, path)),
        _ => Err(format!(
            "`{}` names {} {}s; write more of the path",
            path,
            matches.len(),
            kind
        )),
    }
}

/// The longest run of name characters at the front, and what follows it.
fn word(text: &str) -> (&str, &str) {
    let text = text.trim_start();
    let len = text
        .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == ':'))
        .unwrap_or(text.len());
    text.split_at(len)
}

fn number(text: &str) -> Option<(usize, &str)> {
    let len = text
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(text.len());
    (len > 0).then(|| (text[..len].parse().expect("digits parse"), &text[len..]))
}

fn signed(text: &str) -> Option<(i64, &str)> {
    let (sign, rest) = match text.strip_prefix('-') {
        Some(rest) => (-1, rest),
        None => (1, text),
    };
    let (n, rest) = number(rest)?;
    Some((sign * n as i64, rest))
}

fn head_of(rest: &str) -> String {
    rest.trim_start().chars().take(24).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::term::{Arity, Term};
    use bytecode::assemble;

    fn round_trip(library: &Library, text: &str) -> String {
        let mut ctx = Context::new();
        let term = parse_term(&mut ctx, text, &Scope::new(library))
            .unwrap_or_else(|e| panic!("{}: {}", text, e));
        format!("{}", ctx.display(term))
    }

    #[test]
    fn what_display_writes_is_what_this_reads() {
        let library = Library::new();
        for text in [
            "id(3)",
            "copy(1) ; equal",
            "id(1) * push 1 ; add",
            "copy(1) ; id(1) * not",
            "id(1) * id(1) ; id(2)",
            "(id(1) ; id(1)) * id(1)",
            "id(1) ; (id(1) ; id(1))",
            "id(1) * (id(1) * id(1))",
            "branch { drop(1) ; push true } { id(1) * push 2 ; equal }",
            "swap ; tuple 2 ; as_tuple 2 ; untuple 2",
            "push \"hi\" ; drop(1)",
            "push () ; id(1) * push (1, true) ; drop(2)",
            "push -3 ; is_int",
        ] {
            assert_eq!(round_trip(&library, text), text);
        }
    }

    #[test]
    fn a_call_is_named_rather_than_numbered() {
        let library = assemble(
            r#"
            mod inner { #[arity(1,1)] sentence twice { pick 0 add } }
            "#,
        )
        .unwrap();
        let scope = Scope::new(&library);
        let mut ctx = Context::new();
        let term = parse_term(&mut ctx, "call inner::twice ; not", &scope).unwrap();
        assert_eq!(ctx.arity(term), Arity::new(1, 1));
        // The trailing part is enough while it is unambiguous, and the call
        // carries the callee's inferred arity.
        let again = parse_term(&mut ctx, "call twice", &scope).unwrap();
        let Term::Compose(call, _) = *ctx.get(term) else {
            panic!()
        };
        assert!(ctx.equal(again, call));
        let err = parse_term(&mut ctx, "call nowhere", &scope).unwrap_err();
        assert!(err.contains("no sentence is called"), "{}", err);
    }

    #[test]
    fn a_symbol_is_the_path_it_was_declared_under() {
        let library = assemble("mod inner { symbol tag }").unwrap();
        let mut ctx = Context::new();
        let term = parse_term(&mut ctx, "push inner::tag", &Scope::new(&library)).unwrap();
        assert_eq!(format!("{}", ctx.display(term)), "push inner::tag");
        let err = parse_term(&mut ctx, "push inner::nope", &Scope::new(&library)).unwrap_err();
        assert!(err.contains("no symbol"), "{}", err);
    }

    #[test]
    fn halves_that_do_not_meet_are_refused_rather_than_padded() {
        let library = Library::new();
        let mut ctx = Context::new();
        let err = parse_term(&mut ctx, "copy(1) ; not", &Scope::new(&library)).unwrap_err();
        assert!(err.contains("cannot compose"), "{}", err);
        let err = parse_term(
            &mut ctx,
            "branch { drop(1) } { id(1) }",
            &Scope::new(&library),
        )
        .unwrap_err();
        assert!(err.contains("leave the stack differently"), "{}", err);
    }

    #[test]
    fn the_structural_leaves_are_blocks_and_say_so() {
        let library = Library::new();
        let mut ctx = Context::new();
        let err = parse_term(&mut ctx, "drop ; push 1", &Scope::new(&library)).unwrap_err();
        assert!(err.contains("write `drop(1)`"), "{}", err);
        let err = parse_term(&mut ctx, "dip { not }", &Scope::new(&library)).unwrap_err();
        assert!(err.contains("`*` against `id(n)`"), "{}", err);
        let err = parse_term(&mut ctx, "jump twice", &Scope::new(&library)).unwrap_err();
        assert!(err.contains("`call name`"), "{}", err);
    }
}
