use crate::ast::core;
use crate::ast::sugar::{self, Composer, ModuleExpr};
use crate::ast::{
    ParsedInstruction, ParsedSentence, ParsedValue, PrimitiveType, SentenceDecl, SourceAnnotation,
    SymbolDecl, Target, TypeSpec,
};
use crate::library::{Annotation, Library, SentenceAnnotation, SentenceIndex};
use crate::opcode::Instruction;
use crate::resolve::{ModuleId, ModuleItem, ModuleTree, ResolvedItem};
use crate::source::{Error, FileId, SourceMap, Span};
use crate::value::{Symbol, Value};
use std::collections::{HashMap, HashSet};

pub use crate::resolve::{Path, PathSegment};

/// Token types for the assembly lexer.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Export,
    SymbolKeyword,
    TestKeyword,
    ModKeyword,
    SentenceKeyword,
    FunctionKeyword,
    TypeKeyword,
    EnumKeyword,
    DoubleColon,
    Semicolon,
    Identifier(String),
    StringLiteral(String),
    LBrace,
    RBrace,
    Hash,
    LBracket,
    RBracket,
    LParen,
    RParen,
    Comma,
    Colon,
    Pipe,
    Int(i64),
    Float(f64),
    Bool(bool),
}

/// How a token is written in source, for error messages. `Expected ';', found
/// '}'` beats `Expected Semicolon, found RBrace` when the reader is looking at
/// their own file rather than at this enum.
fn describe(token: &Token) -> String {
    let literal = match token {
        Token::Export => "export",
        Token::SymbolKeyword => "symbol",
        Token::TestKeyword => "test",
        Token::ModKeyword => "mod",
        Token::SentenceKeyword => "sentence",
        Token::FunctionKeyword => "function",
        Token::TypeKeyword => "type",
        Token::EnumKeyword => "enum",
        Token::DoubleColon => "::",
        Token::Semicolon => ";",
        Token::LBrace => "{",
        Token::RBrace => "}",
        Token::Hash => "#",
        Token::LBracket => "[",
        Token::RBracket => "]",
        Token::LParen => "(",
        Token::RParen => ")",
        Token::Comma => ",",
        Token::Colon => ":",
        Token::Pipe => "|",
        Token::Identifier(name) => return format!("`{}`", name),
        Token::StringLiteral(s) => return format!("string literal \"{}\"", s),
        Token::Int(i) => return format!("`{}`", i),
        Token::Float(f) => return format!("`{}`", f),
        Token::Bool(b) => return format!("`{}`", b),
    };
    format!("`{}`", literal)
}

/// A token together with the byte range it occupies in its file.
#[derive(Debug, Clone)]
struct SpannedToken {
    token: Token,
    span: Span,
}

/// Tokenizer split logic. Every token records where it came from, so a parse
/// error can underline the offending word rather than describe it.
fn tokenize(input: &str, file: FileId) -> Result<Vec<SpannedToken>, Error> {
    let mut tokens = Vec::new();
    let mut chars = input.char_indices().peekable();

    // Pushes a token spanning from `start` to wherever the cursor now sits.
    macro_rules! push {
        ($tokens:expr, $start:expr, $chars:expr, $token:expr) => {{
            let end = $chars.peek().map_or(input.len(), |&(i, _)| i);
            $tokens.push(SpannedToken {
                token: $token,
                span: Span::new(file, $start, end),
            });
        }};
    }

    while let Some(&(start, c)) = chars.peek() {
        match c {
            c if c.is_whitespace() => {
                chars.next();
            }
            '/' => {
                chars.next();
                if chars.peek().map(|&(_, c)| c) == Some('/') {
                    chars.next();
                    // Comment, consume until end of line
                    while let Some(&(_, next_c)) = chars.peek() {
                        if next_c == '\n' {
                            break;
                        }
                        chars.next();
                    }
                } else {
                    let end = chars.peek().map_or(input.len(), |&(i, _)| i);
                    return Err(
                        Error::at("unexpected character `/`", Span::new(file, start, end))
                            .with_help("comments start with `//`"),
                    );
                }
            }
            '{' => {
                chars.next();
                push!(tokens, start, chars, Token::LBrace);
            }
            '}' => {
                chars.next();
                push!(tokens, start, chars, Token::RBrace);
            }
            '#' => {
                chars.next();
                push!(tokens, start, chars, Token::Hash);
            }
            '[' => {
                chars.next();
                push!(tokens, start, chars, Token::LBracket);
            }
            ']' => {
                chars.next();
                push!(tokens, start, chars, Token::RBracket);
            }
            '(' => {
                chars.next();
                push!(tokens, start, chars, Token::LParen);
            }
            ')' => {
                chars.next();
                push!(tokens, start, chars, Token::RParen);
            }
            ',' => {
                chars.next();
                push!(tokens, start, chars, Token::Comma);
            }
            ';' => {
                chars.next();
                push!(tokens, start, chars, Token::Semicolon);
            }
            ':' => {
                chars.next();
                if chars.peek().map(|&(_, c)| c) == Some(':') {
                    chars.next();
                    push!(tokens, start, chars, Token::DoubleColon);
                } else {
                    push!(tokens, start, chars, Token::Colon);
                }
            }

            '|' => {
                chars.next();
                push!(tokens, start, chars, Token::Pipe);
            }
            '"' => {
                chars.next(); // consume '"'
                let mut string_val = String::new();
                let mut closed = false;
                for (_, next_c) in chars.by_ref() {
                    if next_c == '"' {
                        closed = true;
                        break;
                    }
                    string_val.push(next_c);
                }
                if !closed {
                    return Err(Error::at(
                        "unclosed string literal",
                        Span::new(file, start, input.len()),
                    ));
                }
                push!(tokens, start, chars, Token::StringLiteral(string_val));
            }
            // Parse negative or positive numbers
            '-' | '0'..='9' => {
                let mut number_str = String::new();
                if c == '-' {
                    number_str.push(chars.next().unwrap().1);
                }

                while let Some(&(_, next_c)) = chars.peek() {
                    if next_c.is_ascii_digit() {
                        number_str.push(chars.next().unwrap().1);
                    } else {
                        break;
                    }
                }

                let mut is_float = false;
                if let Some(&(_, '.')) = chars.peek() {
                    chars.next(); // consume '.'
                    number_str.push('.');
                    is_float = true;

                    while let Some(&(_, next_c)) = chars.peek() {
                        if next_c.is_ascii_digit() {
                            number_str.push(chars.next().unwrap().1);
                        } else {
                            break;
                        }
                    }
                }

                let end = chars.peek().map_or(input.len(), |&(i, _)| i);
                let span = Span::new(file, start, end);
                if is_float {
                    let val = number_str.parse::<f64>().map_err(|e| {
                        Error::at(format!("invalid float `{}`: {}", number_str, e), span)
                    })?;
                    push!(tokens, start, chars, Token::Float(val));
                } else {
                    if number_str == "-" {
                        return Err(Error::at("minus sign without digits", span));
                    }
                    let val = number_str.parse::<i64>().map_err(|e| {
                        Error::at(format!("invalid integer `{}`: {}", number_str, e), span)
                    })?;
                    push!(tokens, start, chars, Token::Int(val));
                }
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut ident = String::new();
                while let Some(&(_, next_c)) = chars.peek() {
                    if next_c.is_ascii_alphanumeric() || next_c == '_' {
                        ident.push(chars.next().unwrap().1);
                    } else {
                        break;
                    }
                }

                let token = match ident.as_str() {
                    "export" => Token::Export,
                    "symbol" => Token::SymbolKeyword,
                    "test" => Token::TestKeyword,
                    "mod" => Token::ModKeyword,
                    "sentence" => Token::SentenceKeyword,
                    "function" => Token::FunctionKeyword,
                    "type" => Token::TypeKeyword,
                    "enum" => Token::EnumKeyword,
                    "true" => Token::Bool(true),
                    "false" => Token::Bool(false),
                    _ => Token::Identifier(ident),
                };
                push!(tokens, start, chars, token);
            }
            other => {
                chars.next();
                let end = chars.peek().map_or(input.len(), |&(i, _)| i);
                return Err(Error::at(
                    format!("unexpected character `{}`", other),
                    Span::new(file, start, end),
                ));
            }
        }
    }

    Ok(tokens)
}

struct TokenStream {
    tokens: Vec<SpannedToken>,
    position: usize,
    /// A zero-width span at the end of the file, for errors that have no
    /// token to point at because the input ran out.
    eof: Span,
}

impl TokenStream {
    fn new(tokens: Vec<SpannedToken>, file: FileId, len: usize) -> Self {
        TokenStream {
            tokens,
            position: 0,
            eof: Span::new(file, len, len),
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position).map(|t| &t.token)
    }

    fn peek_at(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.position + offset).map(|t| &t.token)
    }

    /// Where the next token sits, or end of input. Capture this *before*
    /// consuming, so an error can point at the token that caused it.
    fn span(&self) -> Span {
        self.tokens.get(self.position).map_or(self.eof, |t| t.span)
    }

    fn next(&mut self) -> Option<Token> {
        if self.position < self.tokens.len() {
            let t = self.tokens[self.position].token.clone();
            self.position += 1;
            Some(t)
        } else {
            None
        }
    }

    /// `expected X, found Y` against the token at the cursor, whether or not
    /// there is one.
    fn expected(&self, what: &str) -> Error {
        match self.peek() {
            Some(found) => Error::at(
                format!("expected {}, found {}", what, describe(found)),
                self.span(),
            ),
            None => Error::at(format!("expected {}, found end of input", what), self.eof),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), Error> {
        if self.peek() == Some(&expected) {
            self.next();
            return Ok(());
        }
        Err(self.expected(&describe(&expected)))
    }
}

/// Parses values into ParsedValue AST nodes.
fn parse_value(stream: &mut TokenStream) -> Result<ParsedValue, Error> {
    let err = stream.expected("a value");
    match stream.next() {
        Some(Token::Bool(b)) => Ok(ParsedValue::Bool(b)),
        Some(Token::Int(i)) => Ok(ParsedValue::Int(i)),
        Some(Token::Float(f)) => Ok(ParsedValue::Float(f)),
        Some(Token::Identifier(name)) => {
            let path = parse_path(stream, name)?;
            Ok(ParsedValue::SymbolRef(path))
        }
        Some(Token::LParen) => {
            let mut elements = Vec::new();
            if stream.peek() == Some(&Token::RParen) {
                stream.next(); // consume ')'
                return Ok(ParsedValue::Tuple(elements));
            }

            loop {
                let val = parse_value(stream)?;
                elements.push(val);

                match stream.peek() {
                    Some(&Token::Comma) => {
                        stream.next(); // consume ','
                        if stream.peek() == Some(&Token::RParen) {
                            stream.next(); // consume trailing comma and ')'
                            break;
                        }
                    }
                    Some(&Token::RParen) => {
                        stream.next(); // consume ')'
                        break;
                    }
                    _ => return Err(stream.expected("`,` or `)`")),
                }
            }
            Ok(ParsedValue::Tuple(elements))
        }
        _ => Err(err),
    }
}

fn parse_path(stream: &mut TokenStream, first_ident: String) -> Result<Path, Error> {
    let mut segments = vec![parse_segment(&first_ident)];
    while let Some(&Token::DoubleColon) = stream.peek() {
        stream.next(); // consume '::'
        match stream.peek() {
            Some(Token::Identifier(name)) => {
                segments.push(parse_segment(&name.clone()));
                stream.next();
            }
            _ => return Err(stream.expected("an identifier after `::`")),
        }
    }
    Ok(Path { segments })
}

fn parse_segment(name: &str) -> PathSegment {
    match name {
        "crate" => PathSegment::Crate,
        "super" => PathSegment::Super,
        other => PathSegment::Identifier(other.to_string()),
    }
}

fn parse_type_spec(stream: &mut TokenStream) -> Result<TypeSpec, Error> {
    parse_type_disjunction(stream)
}

fn parse_type_disjunction(stream: &mut TokenStream) -> Result<TypeSpec, Error> {
    let mut left = parse_type_primary(stream)?;
    while stream.peek() == Some(&Token::Pipe) {
        stream.next(); // consume '|'
        let right = parse_type_primary(stream)?;
        match left {
            TypeSpec::Union(ref mut variants) => {
                variants.push(right);
            }
            _ => {
                left = TypeSpec::Union(vec![left, right]);
            }
        }
    }
    Ok(left)
}

fn parse_type_primary(stream: &mut TokenStream) -> Result<TypeSpec, Error> {
    match stream.peek() {
        Some(&Token::LParen) => {
            stream.next(); // consume '('
            let mut elements = Vec::new();
            if stream.peek() != Some(&Token::RParen) {
                loop {
                    elements.push(parse_type_spec(stream)?);
                    match stream.peek() {
                        Some(&Token::Comma) => {
                            stream.next();
                            if stream.peek() == Some(&Token::RParen) {
                                break;
                            }
                        }
                        Some(&Token::RParen) => {
                            break;
                        }
                        _ => return Err(stream.expected("`,` or `)`")),
                    }
                }
            }
            stream.expect(Token::RParen)?;
            Ok(TypeSpec::Tuple(elements))
        }
        Some(&Token::Bool(b)) => {
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::Bool(b)))
        }
        Some(&Token::Int(i)) => {
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::Int(i)))
        }
        Some(&Token::Float(f)) => {
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::Float(f)))
        }
        Some(&Token::SymbolKeyword) => {
            stream.next();
            Ok(TypeSpec::Primitive(PrimitiveType::Symbol))
        }
        Some(Token::Identifier(name)) => {
            let name_cloned = name.clone();
            stream.next(); // consume identifier

            // Check if it's a primitive type keyword (lowercase only)
            match name_cloned.as_str() {
                "int" => Ok(TypeSpec::Primitive(PrimitiveType::Int)),
                "bool" => Ok(TypeSpec::Primitive(PrimitiveType::Bool)),
                "float" => Ok(TypeSpec::Primitive(PrimitiveType::Float)),
                "symbol" => Ok(TypeSpec::Primitive(PrimitiveType::Symbol)),
                "tuple" => Ok(TypeSpec::Primitive(PrimitiveType::Tuple)),
                _ => {
                    // Otherwise, parse it as a path (which could be a user-defined type or a symbol reference)
                    let path = parse_path(stream, name_cloned)?;
                    Ok(TypeSpec::Path(path))
                }
            }
        }
        _ => Err(stream.expected("a type")),
    }
}

/// Parses a target which is either a named label or an inline `{}` block.
fn parse_target(stream: &mut TokenStream) -> Result<Target, Error> {
    match stream.peek() {
        Some(&Token::Identifier(_)) => {
            if let Some(Token::Identifier(name)) = stream.next() {
                let path = parse_path(stream, name)?;
                Ok(Target::Label(path))
            } else {
                unreachable!()
            }
        }
        Some(&Token::LBrace) => {
            let sentence = parse_sentence_body(stream)?;
            Ok(Target::Inline(sentence))
        }
        _ => Err(stream.expected("a label or an inline `{` block")),
    }
}

fn parse_sentence_body(stream: &mut TokenStream) -> Result<ParsedSentence, Error> {
    let open = stream.span();
    stream.expect(Token::LBrace)?;
    let mut instructions = Vec::new();

    while stream.peek() != Some(&Token::RBrace) && stream.peek().is_some() {
        let inst = parse_instruction(stream)?;
        instructions.push(inst);
    }

    // Running out of input mid-body means the brace that opened it was never
    // closed, and that brace is the useful thing to point at — the end of the
    // file tells the reader nothing about which block went wrong.
    if stream.peek().is_none() {
        return Err(Error::at("unclosed `{`", open).with_help("this block has no closing `}`"));
    }
    stream.expect(Token::RBrace)?;
    Ok(ParsedSentence { instructions })
}

fn parse_usize(stream: &mut TokenStream) -> Result<usize, Error> {
    match stream.peek() {
        Some(&Token::Int(val)) if val >= 0 => {
            stream.next();
            Ok(val as usize)
        }
        _ => Err(stream.expected("a non-negative integer")),
    }
}

fn parse_instruction(stream: &mut TokenStream) -> Result<ParsedInstruction, Error> {
    let span = stream.span();
    let err = stream.expected("an instruction");
    let name = match stream.next() {
        Some(Token::Identifier(name)) => name,
        Some(Token::ModKeyword) => "mod".to_string(),
        _ => return Err(err),
    };

    match name.as_str() {
        "push" => {
            let val = parse_value(stream)?;
            Ok(ParsedInstruction::Push(val))
        }
        "drop" => {
            let depth = parse_usize(stream)?;
            Ok(ParsedInstruction::Drop(depth))
        }
        "pick" => {
            let depth = parse_usize(stream)?;
            Ok(ParsedInstruction::Pick(depth))
        }
        "roll" => {
            let depth = parse_usize(stream)?;
            Ok(ParsedInstruction::Roll(depth))
        }
        "equal" => Ok(ParsedInstruction::Equal),
        "greater" => Ok(ParsedInstruction::Greater),
        "less" => Ok(ParsedInstruction::Less),
        "add" => Ok(ParsedInstruction::Add),
        "subtract" | "sub" => Ok(ParsedInstruction::Subtract),
        "multiply" | "mul" => Ok(ParsedInstruction::Multiply),
        "divide" | "div" => Ok(ParsedInstruction::Divide),
        "modulo" | "mod" => Ok(ParsedInstruction::Modulo),
        "not" => Ok(ParsedInstruction::Not),
        "and" => Ok(ParsedInstruction::And),
        "or" => Ok(ParsedInstruction::Or),
        "negate" | "neg" => Ok(ParsedInstruction::Negate),
        "jump" => {
            let target = parse_target(stream)?;
            Ok(ParsedInstruction::Jump(target))
        }
        "dip" => {
            // The count is optional; bare `dip` hides one value, as the
            // classic combinator does.
            let depth = match stream.peek() {
                Some(&Token::Int(_)) => parse_usize(stream)?,
                _ => 1,
            };
            let target = parse_target(stream)?;
            Ok(ParsedInstruction::Dip(depth, target))
        }
        "branch" => {
            let target_true = parse_target(stream)?;
            let target_false = parse_target(stream)?;
            Ok(ParsedInstruction::Branch(target_true, target_false))
        }
        "panic" => Ok(ParsedInstruction::Panic),
        "assert" => Ok(ParsedInstruction::Assert),
        "assert_equal" | "assert_eq" => Ok(ParsedInstruction::AssertEqual),
        "tuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::Tuple(size))
        }
        "untuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::Untuple(size))
        }
        "symbol_len" => Ok(ParsedInstruction::SymbolLen),
        "symbol_char_at" => Ok(ParsedInstruction::SymbolCharAt),
        "is_int" => Ok(ParsedInstruction::IsInt),
        "is_bool" => Ok(ParsedInstruction::IsBool),
        "is_float" => Ok(ParsedInstruction::IsFloat),
        "is_symbol" => Ok(ParsedInstruction::IsSymbol),
        "is_tuple" => Ok(ParsedInstruction::IsTuple),
        "tuple_length" => Ok(ParsedInstruction::TupleLength),
        other => Err(Error::at(format!("unknown instruction `{}`", other), span)),
    }
}

fn parse_module_expr(stream: &mut TokenStream) -> Result<ModuleExpr, Error> {
    if let Some(Token::Identifier(ident)) = stream.peek().cloned()
        && let Some(composer) = Composer::from_name(&ident)
    {
        stream.next(); // consume composer name
        let args = parse_composer_args(stream)?;
        return Ok(ModuleExpr::Composed { composer, args });
    }

    match stream.peek() {
        Some(Token::Identifier(_)) => {
            let first_ident = match stream.next() {
                Some(Token::Identifier(id)) => id,
                _ => unreachable!(),
            };
            let path = parse_path(stream, first_ident)?;
            Ok(ModuleExpr::Named(path))
        }
        Some(_) => {
            let val = parse_value(stream)?;
            Ok(ModuleExpr::Value(val))
        }
        None => Err(stream.expected("a module expression or value")),
    }
}

fn parse_composer_args(stream: &mut TokenStream) -> Result<Vec<ModuleExpr>, Error> {
    stream.expect(Token::LParen)?;
    let mut args = Vec::new();
    if stream.peek() != Some(&Token::RParen) {
        loop {
            args.push(parse_module_expr(stream)?);
            if stream.peek() == Some(&Token::Comma) {
                stream.next();
            } else {
                break;
            }
        }
    }
    stream.expect(Token::RParen)?;
    Ok(args)
}

/// Phase 1: tokenize and parse. Performs no desugaring; the only non-syntactic
/// work is reading the files named by `mod name;`.
///
/// `file` must already be registered in `map`. The map is threaded through
/// rather than returned because `mod name;` registers further files partway
/// into the parse, and an error in one of those has to render against the file
/// it came from.
pub(crate) fn parse_source(
    map: &mut SourceMap,
    file: FileId,
    base_dir: Option<&std::path::Path>,
) -> Result<Vec<sugar::Item>, Error> {
    // Copied out so the map stays free for the nested files `mod name;` adds.
    let input = map.text(file).to_owned();
    let tokens = tokenize(&input, file)?;
    let mut stream = TokenStream::new(tokens, file, input.len());
    parse_items(&mut stream, None, base_dir, map)
}

fn parse_annotations(stream: &mut TokenStream) -> Result<Vec<SourceAnnotation>, Error> {
    let mut annotations = Vec::new();
    while stream.peek() == Some(&Token::Hash) {
        stream.next(); // consume '#'
        stream.expect(Token::LBracket)?;
        let name_span = stream.span();
        let name = match stream.peek() {
            Some(Token::Identifier(name)) => {
                let name = name.clone();
                stream.next();
                name
            }
            _ => return Err(stream.expected("an annotation name")),
        };

        let ann = match name.as_str() {
            "arity" => {
                stream.expect(Token::LParen)?;
                let n = match stream.peek() {
                    Some(&Token::Int(val)) => {
                        stream.next();
                        val
                    }
                    _ => return Err(stream.expected("an integer, the arity's input count")),
                };
                stream.expect(Token::Comma)?;
                let m = match stream.peek() {
                    Some(&Token::Int(val)) => {
                        stream.next();
                        val
                    }
                    _ => return Err(stream.expected("an integer, the arity's output count")),
                };
                stream.expect(Token::RParen)?;
                Annotation::Arity(n, m)
            }
            "precondition" => {
                Annotation::Precondition(parse_annotation_path(stream, "precondition")?)
            }
            "postcondition" => {
                Annotation::Postcondition(parse_annotation_path(stream, "postcondition")?)
            }
            "recursive" => Annotation::Recursive,
            "total" => Annotation::Total,
            other => {
                return Err(
                    Error::at(format!("unsupported annotation `{}`", other), name_span).with_help(
                        "known annotations: arity, precondition, postcondition, recursive, total",
                    ),
                );
            }
        };
        stream.expect(Token::RBracket)?;

        // A declaration carries at most one of each contract. Verification reads
        // a single precondition and a single postcondition, so a second would be
        // silently ignored rather than conjoined. `arity` is exempt because every
        // one of those is checked, and `recursive`/`total` are idempotent flags.
        let has = |f: fn(&SourceAnnotation) -> bool| annotations.iter().any(f);
        let duplicate = match &ann {
            Annotation::Precondition(_) if has(|a| matches!(a, Annotation::Precondition(_))) => {
                Some("precondition")
            }
            Annotation::Postcondition(_) if has(|a| matches!(a, Annotation::Postcondition(_))) => {
                Some("postcondition")
            }
            _ => None,
        };
        if let Some(kind) = duplicate {
            return Err(Error::at(
                format!("duplicate #[{}] on one declaration", kind),
                name_span,
            )
            .with_help("only one is allowed; a second would be ignored rather than conjoined"));
        }

        annotations.push(ann);
    }
    Ok(annotations)
}

fn parse_annotation_path(stream: &mut TokenStream, kind: &str) -> Result<Path, Error> {
    stream.expect(Token::LParen)?;
    let first_ident = match stream.peek() {
        Some(Token::Identifier(s)) => {
            let s = s.clone();
            stream.next();
            s
        }
        _ => return Err(stream.expected(&format!("an identifier, the {} function", kind))),
    };
    let path = parse_path(stream, first_ident)?;
    stream.expect(Token::RParen)?;
    Ok(path)
}

/// Consumes any `export` / `test` markers preceding an item.
fn parse_modifiers(stream: &mut TokenStream) -> (bool, bool) {
    let mut is_exported = false;
    let mut is_test = false;
    loop {
        if stream.peek() == Some(&Token::Export) {
            stream.next();
            is_exported = true;
        } else if stream.peek() == Some(&Token::TestKeyword) {
            stream.next();
            is_test = true;
        } else {
            break;
        }
    }
    (is_exported, is_test)
}

fn expect_name(stream: &mut TokenStream, what: &str) -> Result<String, Error> {
    match stream.peek() {
        Some(Token::Identifier(name)) => {
            let name = name.clone();
            stream.next();
            Ok(name)
        }
        _ => Err(stream.expected(&format!("a {}", what))),
    }
}

fn parse_items(
    stream: &mut TokenStream,
    end_token: Option<Token>,
    base_dir: Option<&std::path::Path>,
    map: &mut SourceMap,
) -> Result<Vec<sugar::Item>, Error> {
    let mut items = Vec::new();

    while stream.peek().is_some() {
        if let Some(ref end) = end_token
            && stream.peek() == Some(end)
        {
            break;
        }

        let item_span = stream.span();
        let annotations = parse_annotations(stream)?;

        // Symbols take no modifiers, so they are recognized before them.
        if annotations.is_empty() && stream.peek() == Some(&Token::SymbolKeyword) {
            stream.next(); // consume 'symbol'
            let name = expect_name(stream, "symbol name")?;
            let debug_desc = match stream.peek() {
                Some(Token::StringLiteral(desc)) => {
                    let desc = desc.clone();
                    stream.next();
                    Some(desc)
                }
                _ => None,
            };
            items.push(sugar::Item::Symbol(SymbolDecl { name, debug_desc }));
            continue;
        }

        // `test mod` is a test machine, not a test sentence, so it is matched
        // before the modifier loop would swallow the `test`.
        let is_test_mod = stream.peek() == Some(&Token::TestKeyword)
            && stream.peek_at(1) == Some(&Token::ModKeyword);
        if is_test_mod || stream.peek() == Some(&Token::ModKeyword) {
            if !annotations.is_empty() {
                return Err(Error::at(
                    "annotations are not supported on modules",
                    item_span,
                ));
            }
            if is_test_mod {
                stream.next(); // consume 'test'
            }
            stream.next(); // consume 'mod'
            items.push(parse_mod_item(stream, is_test_mod, base_dir, map)?);
            continue;
        }

        let (is_exported, is_test) = parse_modifiers(stream);

        if stream.peek() == Some(&Token::TypeKeyword) {
            stream.next(); // consume 'type'
            let name = expect_name(stream, "type name")?;
            let spec = parse_type_spec(stream)?;
            stream.expect(Token::Semicolon)?;
            items.push(sugar::Item::Type(sugar::TypeDecl {
                name,
                spec,
                annotations,
            }));
            continue;
        }

        if stream.peek() == Some(&Token::EnumKeyword) {
            items.push(sugar::Item::Enum(parse_enum_decl(stream, annotations)?));
            continue;
        }

        let is_function = match stream.peek() {
            Some(&Token::SentenceKeyword) => {
                stream.next();
                false
            }
            Some(&Token::FunctionKeyword) => {
                stream.next();
                true
            }
            _ => return Err(stream.expected("`sentence`, `function`, `type`, `enum`, or `mod`")),
        };

        let name = expect_name(stream, "sentence name")?;
        if stream.peek() == Some(&Token::Colon) {
            stream.next();
        }
        let body = parse_sentence_body(stream)?;

        let mut annotations = annotations;
        if is_function {
            annotations.push(Annotation::Arity(1, 1));
        }

        items.push(sugar::Item::Sentence(SentenceDecl {
            name,
            body,
            annotations,
            is_exported,
            is_test,
        }));
    }

    Ok(items)
}

/// Parses what follows `mod`: a composition, an external file, or a block.
fn parse_mod_item(
    stream: &mut TokenStream,
    is_test: bool,
    base_dir: Option<&std::path::Path>,
    map: &mut SourceMap,
) -> Result<sugar::Item, Error> {
    let name_span = stream.span();
    let name = expect_name(stream, "module name")?;

    if let Some(Token::Identifier(ident)) = stream.peek()
        && let Some(composer) = Composer::from_name(ident)
    {
        stream.next(); // consume composer name
        let args = parse_composer_args(stream)?;
        stream.expect(Token::Semicolon)?;
        return Ok(sugar::Item::Compose(sugar::ComposeDecl {
            name,
            composer,
            args,
            is_test,
        }));
    }

    if stream.peek() == Some(&Token::Semicolon) {
        stream.next(); // consume ';'
        let base = base_dir.ok_or_else(|| {
            Error::at(format!("cannot load external module `{}`", name), name_span)
                .with_help("no base directory was given, so there is nowhere to look for the file")
        })?;
        let file_path = base.join(format!("{}.hana", name));
        let file_content = std::fs::read_to_string(&file_path).map_err(|e| {
            Error::at(
                format!("cannot read `{}`: {}", file_path.display(), e),
                name_span,
            )
        })?;

        // Registered before parsing, so an error inside the file renders
        // against the file rather than against whoever included it.
        let included = map.add_path(&file_path, file_content);
        let items = parse_source(map, included, Some(&base.join(&name)))?;
        return Ok(sugar::Item::Mod(sugar::ModDecl {
            name,
            items,
            is_test,
        }));
    }

    stream.expect(Token::LBrace)?;
    let new_base = base_dir.map(|b| b.join(&name));
    let items = parse_items(stream, Some(Token::RBrace), new_base.as_deref(), map)?;
    stream.expect(Token::RBrace)?;
    Ok(sugar::Item::Mod(sugar::ModDecl {
        name,
        items,
        is_test,
    }))
}

fn parse_enum_decl(
    stream: &mut TokenStream,
    annotations: Vec<SourceAnnotation>,
) -> Result<sugar::EnumDecl, Error> {
    stream.expect(Token::EnumKeyword)?;
    let name = expect_name(stream, "enum name")?;
    stream.expect(Token::LBrace)?;

    let mut variants = Vec::new();
    while stream.peek() != Some(&Token::RBrace) {
        let variant_name = expect_name(stream, "variant name")?;

        // The parameter list is required, even when empty: `Case3()`.
        stream.expect(Token::LParen)?;
        let mut elements = Vec::new();
        if stream.peek() != Some(&Token::RParen) {
            loop {
                elements.push(parse_type_spec(stream)?);
                match stream.peek() {
                    Some(&Token::Comma) => {
                        stream.next();
                        if stream.peek() == Some(&Token::RParen) {
                            break;
                        }
                    }
                    Some(&Token::RParen) => break,
                    _ => return Err(stream.expected("`,` or `)`")),
                }
            }
        }
        stream.expect(Token::RParen)?;

        variants.push(sugar::EnumVariant {
            name: variant_name,
            elements,
        });

        // Variants may be followed by an optional comma.
        if stream.peek() == Some(&Token::Comma) {
            stream.next();
        }
    }
    stream.expect(Token::RBrace)?;

    Ok(sugar::EnumDecl {
        name,
        variants,
        annotations,
    })
}

/// Everything the tree-building pass accumulates alongside the module tree
/// itself: the flat sentence list to compile, and the library's lookup maps.
/// Phase 3: declare. Walks the core tree assigning module ids and sentence
/// indices, binding every name, and collecting the library's lookup maps.
struct TreeBuilder {
    tree: ModuleTree,
    symbol_counter: usize,
    sentence_counter: usize,
    /// Each sentence paired with the module its paths resolve against, which
    /// is always simply the module it is declared in.
    flat_sentences: Vec<(ModuleId, SentenceDecl)>,
    exports: HashMap<String, SentenceIndex>,
    tests: HashMap<String, SentenceIndex>,
    test_machines: HashSet<String>,
}

/// Sentences a test machine module exposes to the runtime.
const MACHINE_SENTENCES: [&str; 7] = [
    "init",
    "accept",
    "emit",
    "process",
    "tau_reduce",
    "is_done",
    "is_ready_to_finish",
];

impl TreeBuilder {
    fn new() -> Self {
        Self {
            tree: ModuleTree::new(),
            symbol_counter: 0,
            sentence_counter: 0,
            flat_sentences: Vec::new(),
            exports: HashMap::new(),
            tests: HashMap::new(),
            test_machines: HashSet::new(),
        }
    }

    fn build(&mut self, items: Vec<core::Item>, scope: ModuleId) -> Result<(), String> {
        for item in items {
            match item {
                core::Item::Symbol(decl) => {
                    let desc = decl
                        .debug_desc
                        .unwrap_or_else(|| self.tree.fq_name(scope, &decl.name));
                    let symbol = Value::Symbol(Symbol {
                        id: self.symbol_counter,
                        name: desc,
                    });
                    self.symbol_counter += 1;

                    self.tree
                        .declare(scope, decl.name, ModuleItem::Symbol(symbol))?;
                }
                core::Item::Sentence(decl) => {
                    let s_idx = SentenceIndex::from(self.sentence_counter);
                    self.sentence_counter += 1;

                    self.tree
                        .declare(scope, decl.name.clone(), ModuleItem::Sentence(s_idx))?;

                    let fq_name = self.tree.fq_name(scope, &decl.name);
                    if decl.is_exported {
                        self.exports.insert(fq_name.clone(), s_idx);
                    }
                    if decl.is_test {
                        self.tests.insert(fq_name, s_idx);
                    }

                    self.flat_sentences.push((scope, decl));
                }
                core::Item::Mod(decl) => {
                    let sub_id = self.tree.declare_module(scope, decl.name)?;
                    self.build(decl.items, sub_id)?;
                    if decl.is_test {
                        self.register_test_machine(sub_id, decl.exports_machine_sentences)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Registers a `test mod` as a machine the runtime can drive. Composed
    /// machines additionally export their machine sentences, since the generated
    /// bodies have no `export` markers of their own.
    fn register_test_machine(
        &mut self,
        module: ModuleId,
        export_machine_sentences: bool,
    ) -> Result<(), String> {
        let fq_path = self.tree.path_of(module).join("::");
        if self.tree.sentence(module, "init").is_none() {
            return Err(format!(
                "Test mod '{}' must export an 'init' sentence",
                fq_path
            ));
        }
        self.test_machines.insert(fq_path);

        if export_machine_sentences {
            for name in MACHINE_SENTENCES {
                if let Some(s_idx) = self.tree.sentence(module, name) {
                    self.exports.insert(self.tree.fq_name(module, name), s_idx);
                }
            }
        }
        Ok(())
    }
}

struct Compiler<'a> {
    tree: &'a ModuleTree,
    sentences: Vec<Vec<Instruction>>,
    names: Vec<String>,
    annotations: Vec<Vec<SentenceAnnotation>>,
    current_parent_idx: Option<SentenceIndex>,
}

impl<'a> Compiler<'a> {
    /// Resolves the paths a sentence's contract annotations name, against the
    /// module the sentence is declared in — the same scope its body uses.
    fn resolve_annotations(
        &self,
        scope: ModuleId,
        annotations: &[SourceAnnotation],
    ) -> Result<Vec<SentenceAnnotation>, String> {
        annotations
            .iter()
            .map(|ann| {
                Ok(match ann {
                    Annotation::Precondition(path) => Annotation::Precondition(
                        self.resolve_contract_fn("precondition", scope, path)?,
                    ),
                    Annotation::Postcondition(path) => Annotation::Postcondition(
                        self.resolve_contract_fn("postcondition", scope, path)?,
                    ),
                    Annotation::Arity(n, m) => Annotation::Arity(*n, *m),
                    Annotation::Recursive => Annotation::Recursive,
                    Annotation::Total => Annotation::Total,
                })
            })
            .collect()
    }

    fn resolve_contract_fn(
        &self,
        kind: &str,
        scope: ModuleId,
        path: &Path,
    ) -> Result<SentenceIndex, String> {
        match self
            .tree
            .resolve(scope, path)
            .map_err(|e| format!("unresolved {} '{}': {}", kind, path, e))?
        {
            ResolvedItem::Sentence(idx) => Ok(idx),
            ResolvedItem::Symbol(_) => Err(format!(
                "{} '{}' names a symbol, but must name a sentence",
                kind, path
            )),
        }
    }

    fn compile_value(&self, scope: ModuleId, parsed: ParsedValue) -> Result<Value, String> {
        match parsed {
            ParsedValue::Bool(b) => Ok(Value::Bool(b)),
            ParsedValue::Int(i) => Ok(Value::Int(i)),
            ParsedValue::Float(f) => Ok(Value::Float(f)),
            ParsedValue::Tuple(elements) => {
                let mut compiled_elements = Vec::new();
                for elem in elements {
                    compiled_elements.push(self.compile_value(scope, elem)?);
                }
                Ok(Value::Tuple(compiled_elements))
            }
            ParsedValue::SymbolRef(path) => match self.tree.resolve(scope, &path)? {
                ResolvedItem::Symbol(val) => Ok(val),
                ResolvedItem::Sentence(_) => Err(format!(
                    "Expected symbol, found sentence at path {:?}",
                    path
                )),
            },
        }
    }

    fn compile_sentence_body(
        &mut self,
        scope: ModuleId,
        instructions: Vec<ParsedInstruction>,
    ) -> Result<Vec<Instruction>, String> {
        let mut compiled = Vec::new();
        for inst in instructions {
            let c_inst = match inst {
                ParsedInstruction::Push(v) => {
                    let compiled_val = self.compile_value(scope, v)?;
                    Instruction::Push(compiled_val)
                }
                ParsedInstruction::Drop(0) => Instruction::Drop,
                ParsedInstruction::Drop(d) => {
                    // Reaching below the top is a dip around a plain drop.
                    let target = Target::Inline(ParsedSentence {
                        instructions: vec![ParsedInstruction::Drop(0)],
                    });
                    let target_idx = self.resolve_target(scope, target)?;
                    Instruction::Dip(d, target_idx)
                }
                ParsedInstruction::Pick(d) => Instruction::Pick(d),
                ParsedInstruction::Roll(d) => Instruction::Roll(d),
                ParsedInstruction::Equal => Instruction::Equal,
                ParsedInstruction::Greater => Instruction::Greater,
                ParsedInstruction::Less => Instruction::Less,
                ParsedInstruction::Add => Instruction::Add,
                ParsedInstruction::Subtract => Instruction::Subtract,
                ParsedInstruction::Multiply => Instruction::Multiply,
                ParsedInstruction::Divide => Instruction::Divide,
                ParsedInstruction::Modulo => Instruction::Modulo,
                ParsedInstruction::Not => Instruction::Not,
                ParsedInstruction::Negate => Instruction::Negate,
                ParsedInstruction::Panic => Instruction::Panic,
                ParsedInstruction::Assert => Instruction::Assert,
                ParsedInstruction::AssertEqual => Instruction::AssertEqual,
                ParsedInstruction::Tuple(n) => Instruction::Tuple(n),
                ParsedInstruction::Untuple(n) => Instruction::Untuple(n),
                ParsedInstruction::And => Instruction::And,
                ParsedInstruction::Or => Instruction::Or,
                ParsedInstruction::SymbolLen => Instruction::SymbolLen,
                ParsedInstruction::SymbolCharAt => Instruction::SymbolCharAt,
                ParsedInstruction::IsInt => Instruction::IsInt,
                ParsedInstruction::IsBool => Instruction::IsBool,
                ParsedInstruction::IsFloat => Instruction::IsFloat,
                ParsedInstruction::IsSymbol => Instruction::IsSymbol,
                ParsedInstruction::IsTuple => Instruction::IsTuple,
                ParsedInstruction::TupleLength => Instruction::TupleLength,
                ParsedInstruction::Jump(target) => {
                    let target_idx = self.resolve_target(scope, target)?;
                    // A plain call is a dip with an empty hidden region.
                    Instruction::Dip(0, target_idx)
                }
                ParsedInstruction::Dip(depth, target) => {
                    let target_idx = self.resolve_target(scope, target)?;
                    Instruction::Dip(depth, target_idx)
                }
                ParsedInstruction::Branch(t1, t2) => {
                    let idx1 = self.resolve_target(scope, t1)?;
                    let idx2 = self.resolve_target(scope, t2)?;
                    Instruction::Branch(idx1, idx2)
                }
                ParsedInstruction::TypeCheckPath(path) => {
                    let resolved = match self.tree.resolve(scope, &path) {
                        Ok(res) => res,
                        Err(e) => {
                            let mut check_path = path.clone();
                            check_path
                                .segments
                                .push(PathSegment::Identifier("check".to_string()));
                            self.tree.resolve(scope, &check_path).map_err(|_| {
                                format!("Could not resolve type path '{}': {}", path, e)
                            })?
                        }
                    };
                    match resolved {
                        ResolvedItem::Sentence(idx) => Instruction::Dip(0, idx),
                        ResolvedItem::Symbol(val) => {
                            compiled.push(Instruction::Push(val));
                            Instruction::Equal
                        }
                    }
                }
            };
            compiled.push(c_inst);
        }
        Ok(compiled)
    }

    fn resolve_target(&mut self, scope: ModuleId, target: Target) -> Result<SentenceIndex, String> {
        match target {
            Target::Label(path) => {
                match self
                    .tree
                    .resolve(scope, &path)
                    .map_err(|e| format!("Unresolved label target: {}", e))?
                {
                    ResolvedItem::Sentence(idx) => Ok(idx),
                    ResolvedItem::Symbol(_) => Err(format!(
                        "Expected sentence, found symbol at path {:?}",
                        path
                    )),
                }
            }
            Target::Inline(parsed_sentence) => {
                let new_idx = SentenceIndex::from(self.sentences.len());
                self.sentences.push(Vec::new());
                self.names.push("<inline>".to_string());

                // A branch arm or dip body is part of the sentence that wrote
                // it, so the annotations that change how its instructions
                // compile have to follow it in.
                let mut inline_anns = Vec::new();
                if let Some(parent_idx) = self.current_parent_idx {
                    let parent_idx_usize: usize = parent_idx.into();
                    if parent_idx_usize < self.annotations.len()
                        && self.annotations[parent_idx_usize].contains(&Annotation::Recursive)
                    {
                        inline_anns.push(Annotation::Recursive);
                    }
                }
                self.annotations.push(inline_anns);

                let prev_parent = self.current_parent_idx;
                self.current_parent_idx = Some(new_idx);
                let compiled_body = self.compile_sentence_body(scope, parsed_sentence.instructions);
                self.current_parent_idx = prev_parent;

                let compiled_body = compiled_body?;
                let idx_usize: usize = new_idx.into();
                self.sentences[idx_usize] = compiled_body;
                Ok(new_idx)
            }
        }
    }
}

/// Assembles the input text into a `Library`, rendering any error as text.
///
/// A convenience for callers with a single source string and no file on disk;
/// it registers the input as `<input>` in a throwaway map. Callers that have
/// real files should use [`assemble_source`] so errors name them.
pub fn assemble(input: &str) -> Result<Library, String> {
    assemble_with_path(input, None)
}

/// Assembles the input text with an optional base directory context for resolving external modules.
pub fn assemble_with_path(
    input: &str,
    base_dir: Option<&std::path::Path>,
) -> Result<Library, String> {
    let mut map = SourceMap::new();
    let file = map.add("<input>", input.to_string());
    assemble_source(&mut map, file, base_dir).map_err(|e| map.render(&e))
}

/// Assembles a source file already registered in `map`.
///
/// The caller owns the map so it outlives assembly: rendering an error needs
/// the text of whichever file it came from, including files pulled in by
/// `mod name;` partway through the parse.
pub fn assemble_source(
    map: &mut SourceMap,
    file: FileId,
    base_dir: Option<&std::path::Path>,
) -> Result<Library, Error> {
    let parsed = parse_source(map, file, base_dir)?;
    let items = crate::lower::lower_items(parsed)?;

    let mut builder = TreeBuilder::new();
    builder.build(items, crate::resolve::ROOT)?;

    let TreeBuilder {
        tree,
        sentence_counter,
        flat_sentences,
        exports,
        tests,
        test_machines,
        ..
    } = builder;

    let mut compiler = Compiler {
        tree: &tree,
        sentences: Vec::new(),
        names: Vec::new(),
        annotations: Vec::new(),
        current_parent_idx: None,
    };

    // Pre-allocate space for all named sentences
    compiler.sentences.resize(sentence_counter, Vec::new());
    compiler.names.resize(sentence_counter, String::new());
    compiler.annotations.resize(sentence_counter, Vec::new());

    // Compile instructions recursively
    for (idx, (scope, sentence)) in flat_sentences.into_iter().enumerate() {
        compiler.annotations[idx] = compiler
            .resolve_annotations(scope, &sentence.annotations)
            .map_err(|e| format!("In '{}': {}", tree.fq_name(scope, &sentence.name), e))?;
        compiler.current_parent_idx = Some(SentenceIndex::from(idx));
        let compiled_instructions =
            compiler.compile_sentence_body(scope, sentence.body.instructions)?;
        compiler.sentences[idx] = compiled_instructions;
        compiler.names[idx] = tree.fq_name(scope, &sentence.name);
    }

    let mut library = Library::new();
    for s in compiler.sentences {
        library.sentences.push(s);
    }

    let mut final_annotations = typed_index_collections::TiVec::new();
    for ann in compiler.annotations {
        final_annotations.push(ann);
    }
    final_annotations.resize(library.sentences.len(), Vec::new());

    let mut final_names = typed_index_collections::TiVec::new();
    for n in compiler.names {
        final_names.push(n);
    }
    library.names = final_names;
    library.exports = exports;
    library.tests = tests;
    library.test_machines = test_machines;
    library.annotations = final_annotations;

    library.symbols = tree.symbol_map();

    crate::arity::check_arities(&mut library)?;
    crate::arity::check_totality(&library)?;

    Ok(library)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parses `input` and returns the rendered error, which is what a user
    /// actually sees.
    fn error_for(input: &str) -> String {
        let mut map = SourceMap::new();
        let file = map.add("main.hana", input.to_string());
        let err = parse_source(&mut map, file, None).expect_err("expected a parse error");
        map.render(&err)
    }

    fn spans(input: &str) -> Vec<(Token, &str)> {
        let mut map = SourceMap::new();
        let file = map.add("main.hana", input.to_string());
        tokenize(input, file)
            .unwrap()
            .into_iter()
            .map(|t| (t.token, &input[t.span.start as usize..t.span.end as usize]))
            .collect()
    }

    #[test]
    fn every_token_spans_exactly_its_own_text() {
        let toks = spans("sentence a { push -12 add }");
        let slices: Vec<&str> = toks.iter().map(|(_, s)| *s).collect();
        assert_eq!(
            slices,
            vec!["sentence", "a", "{", "push", "-12", "add", "}"]
        );
    }

    #[test]
    fn spans_survive_comments_and_blank_lines() {
        let toks = spans("// leading\n\n  push  3.5\n");
        let slices: Vec<&str> = toks.iter().map(|(_, s)| *s).collect();
        assert_eq!(slices, vec!["push", "3.5"]);
    }

    #[test]
    fn a_string_literal_spans_its_quotes() {
        let toks = spans("symbol s \"a desc\"");
        assert_eq!(toks.last().unwrap().1, "\"a desc\"");
    }

    #[test]
    fn multibyte_text_does_not_shift_later_spans() {
        // The comment holds four bytes but two characters; the tokens after it
        // must still slice their own text.
        let toks = spans("// ää\npush 1\n");
        let slices: Vec<&str> = toks.iter().map(|(_, s)| *s).collect();
        assert_eq!(slices, vec!["push", "1"]);
    }

    #[test]
    fn an_error_points_at_the_offending_token() {
        let rendered = error_for("sentence a {\n    add {\n}\n");
        assert!(rendered.contains("--> main.hana:2:9"), "{}", rendered);
        assert!(rendered.contains("|         ^\n"), "{}", rendered);
    }

    #[test]
    fn an_unknown_instruction_underlines_the_whole_word() {
        let rendered = error_for("sentence a {\n    frobnicate\n}\n");
        assert!(
            rendered.contains("unknown instruction `frobnicate`"),
            "{}",
            rendered
        );
        assert!(rendered.contains("^^^^^^^^^^"), "{}", rendered);
    }

    #[test]
    fn an_unclosed_block_points_at_its_opening_brace() {
        // Not at the end of the file, which would say nothing about which
        // block was left open.
        let rendered = error_for("sentence a {\n    push 1\n");
        assert!(rendered.contains("unclosed `{`"), "{}", rendered);
        assert!(rendered.contains("--> main.hana:1:12"), "{}", rendered);
    }

    #[test]
    fn running_out_of_input_points_at_the_end() {
        let rendered = error_for("sentence");
        assert!(rendered.contains("found end of input"), "{}", rendered);
        assert!(rendered.contains("--> main.hana:1:9"), "{}", rendered);
    }

    #[test]
    fn a_lexer_error_is_spanned_too() {
        let rendered = error_for("sentence a {\n    push 1 @ 2\n}\n");
        assert!(
            rendered.contains("unexpected character `@`"),
            "{}",
            rendered
        );
        assert!(rendered.contains("--> main.hana:2:12"), "{}", rendered);
    }

    #[test]
    fn errors_name_tokens_as_written_not_as_variants() {
        let rendered = error_for("sentence a { push 1 } }");
        assert!(rendered.contains("`}`"), "{}", rendered);
        assert!(!rendered.contains("RBrace"), "{}", rendered);
    }

    #[test]
    fn an_error_in_an_included_file_names_that_file() {
        let dir = std::env::temp_dir().join("hanoi_span_include_test");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let main = dir.join("main.hana");
        std::fs::write(&main, "mod helper;\n").unwrap();
        std::fs::write(dir.join("helper.hana"), "sentence v {\n    add {\n}\n").unwrap();

        let mut map = SourceMap::new();
        let root = map.add_path(&main, std::fs::read_to_string(&main).unwrap());
        let err = parse_source(&mut map, root, main.parent()).expect_err("expected an error");
        let rendered = map.render(&err);

        assert!(rendered.contains("helper.hana:2:9"), "{}", rendered);
        // The snippet comes from the included file, not from the includer.
        assert!(rendered.contains("|     add {"), "{}", rendered);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_missing_module_file_points_at_the_module_name() {
        let dir = std::env::temp_dir().join("hanoi_span_missing_test");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let main = dir.join("main.hana");
        std::fs::write(&main, "mod nowhere;\n").unwrap();

        let mut map = SourceMap::new();
        let root = map.add_path(&main, std::fs::read_to_string(&main).unwrap());
        let err = parse_source(&mut map, root, main.parent()).expect_err("expected an error");
        let rendered = map.render(&err);

        assert!(rendered.contains("cannot read"), "{}", rendered);
        assert!(rendered.contains("main.hana:1:5"), "{}", rendered);

        let _ = std::fs::remove_dir_all(&dir);
    }
}
