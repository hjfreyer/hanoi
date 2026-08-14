use crate::arity::EarlyReturn;
use crate::ast::core;
use crate::ast::sugar::{self, Composer, ModuleExpr};
use crate::ast::{
    ConstStringDecl, IdentityDecl, ParsedInstruction, ParsedSentence, ParsedValue, PrimitiveType,
    SentenceDecl, SourceAnnotation, SymbolDecl, Target, TypeSpec,
};
use crate::library::{
    Annotation, Identity, IdentityIndex, Library, SentenceAnnotation, SentenceIndex,
};
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
    ConstStringKeyword,
    TestKeyword,
    ModKeyword,
    SentenceKeyword,
    FunctionKeyword,
    TypeKeyword,
    EnumKeyword,
    IdentityKeyword,
    DoubleColon,
    Equals,
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
    Question,
    Int(i64),
    Bool(bool),
}

/// How a token is written in source, for error messages. `Expected ';', found
/// '}'` beats `Expected Semicolon, found RBrace` when the reader is looking at
/// their own file rather than at this enum.
fn describe(token: &Token) -> String {
    let literal = match token {
        Token::Export => "export",
        Token::SymbolKeyword => "symbol",
        Token::ConstStringKeyword => "const_string",
        Token::TestKeyword => "test",
        Token::ModKeyword => "mod",
        Token::SentenceKeyword => "sentence",
        Token::FunctionKeyword => "function",
        Token::TypeKeyword => "type",
        Token::EnumKeyword => "enum",
        Token::IdentityKeyword => "identity",
        Token::DoubleColon => "::",
        Token::Equals => "=",
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
        Token::Question => "?",
        Token::Identifier(name) => return format!("`{}`", name),
        Token::StringLiteral(s) => return format!("string literal \"{}\"", s),
        Token::Int(i) => return format!("`{}`", i),
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
            // Only an `identity` uses this, and only between its two sides.
            // Nothing else in the language writes `=`, so it needs no
            // lookahead to tell it from `==`, which is spelled `equal`.
            '=' => {
                chars.next();
                push!(tokens, start, chars, Token::Equals);
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
            '?' => {
                chars.next();
                push!(tokens, start, chars, Token::Question);
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

                let end = chars.peek().map_or(input.len(), |&(i, _)| i);
                let span = Span::new(file, start, end);
                if number_str == "-" {
                    return Err(Error::at("minus sign without digits", span));
                }
                let val = number_str.parse::<i64>().map_err(|e| {
                    Error::at(format!("invalid integer `{}`: {}", number_str, e), span)
                })?;
                push!(tokens, start, chars, Token::Int(val));
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
                    "const_string" => Token::ConstStringKeyword,
                    "test" => Token::TestKeyword,
                    "mod" => Token::ModKeyword,
                    "sentence" => Token::SentenceKeyword,
                    "function" => Token::FunctionKeyword,
                    "type" => Token::TypeKeyword,
                    "enum" => Token::EnumKeyword,
                    "identity" => Token::IdentityKeyword,
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
///
/// A tuple literal is written in the order `tuple n` would have taken its
/// elements off the stack, so `push (1, 2)` is `push 1 ; push 2 ; tuple 2` —
/// see [`crate::value::Value::Tuple`].
fn parse_value(stream: &mut TokenStream) -> Result<ParsedValue, Error> {
    let err = stream.expected("a value");
    match stream.next() {
        Some(Token::Bool(b)) => Ok(ParsedValue::Bool(b)),
        Some(Token::Int(i)) => Ok(ParsedValue::Int(i)),
        Some(Token::StringLiteral(s)) => Ok(ParsedValue::ConstString(s)),
        Some(Token::Identifier(name)) => {
            let path = parse_path(stream, name)?;
            Ok(ParsedValue::Ref(path))
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
        Some(Token::StringLiteral(s)) => {
            let s = s.clone();
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::ConstString(s)))
        }
        Some(&Token::SymbolKeyword) => {
            stream.next();
            Ok(TypeSpec::Primitive(PrimitiveType::Symbol))
        }
        Some(&Token::ConstStringKeyword) => {
            stream.next();
            Ok(TypeSpec::Primitive(PrimitiveType::ConstString))
        }
        Some(Token::Identifier(name)) => {
            let name_cloned = name.clone();
            stream.next(); // consume identifier

            // Check if it's a primitive type keyword (lowercase only)
            match name_cloned.as_str() {
                "int" => Ok(TypeSpec::Primitive(PrimitiveType::Int)),
                "bool" => Ok(TypeSpec::Primitive(PrimitiveType::Bool)),
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
    // The one instruction that is punctuation rather than a word, because it
    // reads as a suffix on the call that produced the result.
    if stream.peek() == Some(&Token::Question) {
        stream.next();
        return Ok(ParsedInstruction::Try);
    }
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
        // The two depths that are instructions rather than expansions, so that
        // code which means the primitive can say so. `pick 0` and `roll 1`
        // compile to exactly these and stay the way to write them at a depth.
        "copy" => Ok(ParsedInstruction::Pick(0)),
        "swap" => Ok(ParsedInstruction::Roll(1)),
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
        "tuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::Tuple(size))
        }
        "untuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::Untuple(size))
        }
        "const_string_len" => Ok(ParsedInstruction::ConstStringLen),
        "const_string_char_at" => Ok(ParsedInstruction::ConstStringCharAt),
        "is_int" => Ok(ParsedInstruction::IsInt),
        "is_bool" => Ok(ParsedInstruction::IsBool),
        "is_const_string" => Ok(ParsedInstruction::IsConstString),
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
            // `total` claimed a sentence could not fail. Nothing can fail now
            // — `panic`, `assert` and `assert_eq` are gone — so every sentence
            // is total and the claim says nothing.
            "total" => {
                return Err(Error::at(
                    "`#[total]` is not an annotation: nothing can fail".to_string(),
                    name_span,
                )
                .with_help(
                    "the instructions that could halt a run are gone, so every \
                     sentence is total and there is nothing to claim",
                ));
            }
            // `recursive` was the annotation that let a sentence reach itself.
            // Recursion is forbidden now, so the word is not an annotation
            // whose spelling went wrong — it is a thing the language stopped
            // having, and saying so beats listing what else it could have been.
            "recursive" => {
                return Err(Error::at(
                    "`#[recursive]` is not an annotation: recursion is forbidden".to_string(),
                    name_span,
                )
                .with_help(
                    "a sentence may not reach itself, so a loop is written out as the \
                     steps it takes",
                ));
            }
            other => {
                return Err(
                    Error::at(format!("unsupported annotation `{}`", other), name_span)
                        .with_help("known annotations: arity, precondition, postcondition"),
                );
            }
        };
        stream.expect(Token::RBracket)?;

        // A declaration carries at most one of each contract. Verification reads
        // a single precondition and a single postcondition, so a second would be
        // silently ignored rather than conjoined. `arity` is exempt because every
        // one of those is checked.
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

        // Constants take no modifiers, so they are recognized before them.
        if annotations.is_empty() && stream.peek() == Some(&Token::SymbolKeyword) {
            stream.next(); // consume 'symbol'
            let name = expect_name(stream, "symbol name")?;
            // A symbol used to carry a description, which was also the text
            // `symbol_len` read. Text is a `const_string` now, so the old
            // spelling is refused rather than quietly ignored.
            if let Some(Token::StringLiteral(text)) = stream.peek() {
                let text = text.clone();
                return Err(
                    Error::at("a symbol carries no text", stream.span()).with_help(format!(
                        "a symbol is a unique identity and prints as its own path; \
                         write `const_string {} {:?}` for text a program reads",
                        name, text
                    )),
                );
            }
            items.push(sugar::Item::Symbol(SymbolDecl { name }));
            continue;
        }

        if annotations.is_empty() && stream.peek() == Some(&Token::ConstStringKeyword) {
            stream.next(); // consume 'const_string'
            let name = expect_name(stream, "const string name")?;
            let text = match stream.peek() {
                Some(Token::StringLiteral(text)) => {
                    let text = text.clone();
                    stream.next();
                    text
                }
                // The text is the declaration: a const string without one would
                // be a symbol written the long way round.
                _ => return Err(stream.expected("a string literal, the const string's text")),
            };
            items.push(sugar::Item::ConstString(ConstStringDecl { name, text }));
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

        // `identity name { A } = { B };`. Matched after the modifier loop so
        // that `export identity foo` is refused with a reason rather than
        // reported as a stray `export`.
        if stream.peek() == Some(&Token::IdentityKeyword) {
            stream.next(); // consume 'identity'
            let name_span = stream.span();
            let name = expect_name(stream, "identity name")?;
            let lhs = parse_sentence_body(stream)?;
            stream.expect(Token::Equals)?;
            let rhs = parse_sentence_body(stream)?;
            stream.expect(Token::Semicolon)?;
            if is_exported || is_test {
                return Err(
                    Error::at("an identity takes no `export` or `test` marker", item_span)
                        .with_help(
                            "an identity is a claim about two programs, not a program: \
                     nothing calls it and nothing runs it",
                        ),
                );
            }
            check_identity_annotations(&annotations, item_span)?;
            items.push(sugar::Item::Identity(IdentityDecl {
                name,
                lhs,
                rhs,
                annotations,
                span: name_span,
            }));
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
            _ => {
                return Err(
                    stream.expected("`sentence`, `function`, `type`, `enum`, `identity`, or `mod`")
                );
            }
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

/// The annotations an identity may carry.
///
/// `#[arity(n, m)]` pins the shape both sides must have. The rest name
/// properties of a sentence *being called* — which an identity is not — so they
/// are refused rather than ignored, on the principle that an annotation nothing
/// reads is a lie.
fn check_identity_annotations(annotations: &[SourceAnnotation], span: Span) -> Result<(), Error> {
    for ann in annotations {
        let (name, why) = match ann {
            Annotation::Arity(..) => continue,
            Annotation::Precondition(_) => (
                "precondition",
                "a contract constrains what a caller may pass; an identity has no caller",
            ),
            Annotation::Postcondition(_) => (
                "postcondition",
                "a contract constrains what a caller may pass; an identity has no caller",
            ),
        };
        return Err(
            Error::at(format!("`#[{}]` is not an identity annotation", name), span)
                .with_help(format!("{}. `#[arity(n, m)]` is the one that is", why)),
        );
    }
    Ok(())
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
    /// In declaration order, which is the order `IdentityIndex` counts in.
    identities: Vec<Identity>,
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
            identities: Vec::new(),
        }
    }

    fn build(&mut self, items: Vec<core::Item>, scope: ModuleId) -> Result<(), String> {
        for item in items {
            match item {
                core::Item::Symbol(decl) => {
                    // The path is only how the symbol prints; `id` is what it
                    // is. Both are settled here, where the declaring module is
                    // known.
                    let symbol = Value::Symbol(Symbol {
                        id: self.symbol_counter,
                        path: self.tree.fq_name(scope, &decl.name),
                    });
                    self.symbol_counter += 1;

                    self.tree
                        .declare(scope, decl.name, ModuleItem::Const(symbol))?;
                }
                core::Item::ConstString(decl) => {
                    self.tree.declare(
                        scope,
                        decl.name,
                        ModuleItem::Const(Value::ConstString(decl.text)),
                    )?;
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
                core::Item::Identity(decl) => {
                    // Two sentences, allocated and pushed in lockstep. Phase 4
                    // relies on `flat_sentences[i]` being `SentenceIndex(i)`,
                    // so nothing may come between the counter bumps and the
                    // pushes — a sentence compiled into the wrong slot fails
                    // silently and much later.
                    let lhs = SentenceIndex::from(self.sentence_counter);
                    let rhs = SentenceIndex::from(self.sentence_counter + 1);
                    self.sentence_counter += 2;

                    let id = IdentityIndex::from(self.identities.len());
                    // Into the single per-module namespace, so `identity foo`
                    // and `sentence foo` in one module collide. That is what
                    // makes a fully qualified identity name denote one thing —
                    // which is what anything citing the claim names.
                    let fq_name = self.tree.fq_name(scope, &decl.name);
                    self.tree
                        .declare(scope, decl.name.clone(), ModuleItem::Identity(id))?;
                    self.identities.push(Identity {
                        name: fq_name,
                        lhs,
                        rhs,
                        span: decl.span,
                    });

                    // Named `<identity>::lhs` and `::rhs`, which phase 4 turns
                    // into fully qualified names for free. Nothing resolves to
                    // them — they are not in the module tree — but they are in
                    // `Library::names`, so a tool that works on one side of a
                    // claim can address it by name.
                    for (suffix, body) in [("lhs", decl.lhs), ("rhs", decl.rhs)] {
                        self.flat_sentences.push((
                            scope,
                            SentenceDecl {
                                name: format!("{}::{}", decl.name, suffix),
                                body,
                                annotations: decl.annotations.clone(),
                                is_exported: false,
                                is_test: false,
                            },
                        ));
                    }
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
    /// Every `?` met so far, in the order their expansions were completed,
    /// which puts a nested one before the one that encloses it.
    early_returns: Vec<EarlyReturn>,
    /// The sentence being compiled, for errors about the blocks inside it.
    current_sentence: String,
    /// One block per (reach, depth), shared by every site that expands to it.
    ///
    /// `roll 3` written in two places is the same three instructions either
    /// time, and the blocks they nest through hold nothing that came from the
    /// site. So the whole corpus pays for one chain per depth rather than one
    /// per use — which is what makes the expansion cost `O(deepest reach)`
    /// across a program rather than `O(d)` at every mention of it.
    reaches: HashMap<(Reach, usize), SentenceIndex>,
    /// The same, for the frames a `dip N { ... }` nests through. Keyed by the
    /// target too, since these wrap a particular callee rather than a shape.
    frames: HashMap<(usize, SentenceIndex), SentenceIndex>,
}

/// What a depth-carrying movement instruction does with the value it reaches.
///
/// The three share one recursion — reach past the top value with a frame, do
/// the same thing one shallower inside it — and differ only in where they
/// bottom out and whether the answer has to be brought back up. See
/// [`Compiler::reach`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Reach {
    /// `pick d`: leave the value where it is and bring a copy up.
    Copy,
    /// `roll d`: bring the value itself up.
    Move,
    /// `drop d`: discard it, bringing nothing up.
    Discard,
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
        let resolved = self
            .tree
            .resolve(scope, path)
            .map_err(|e| format!("unresolved {} '{}': {}", kind, path, e))?;
        match resolved {
            ResolvedItem::Sentence(idx) => Ok(idx),
            other => Err(format!(
                "{} '{}' names a {}, but must name a sentence",
                kind,
                path,
                other.describe()
            )),
        }
    }

    fn compile_value(&self, scope: ModuleId, parsed: ParsedValue) -> Result<Value, String> {
        match parsed {
            ParsedValue::Bool(b) => Ok(Value::Bool(b)),
            ParsedValue::Int(i) => Ok(Value::Int(i)),
            ParsedValue::ConstString(s) => Ok(Value::ConstString(s)),
            ParsedValue::Tuple(elements) => {
                let mut compiled_elements = Vec::new();
                for elem in elements {
                    compiled_elements.push(self.compile_value(scope, elem)?);
                }
                Ok(Value::Tuple(compiled_elements))
            }
            ParsedValue::Ref(path) => match self.tree.resolve(scope, &path)? {
                ResolvedItem::Const(val) => Ok(val),
                ResolvedItem::Sentence(_) => Err(format!(
                    "Expected a value, found sentence at path {:?}",
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
        let mut rest = instructions.into_iter();
        while let Some(inst) = rest.next() {
            let c_inst = match inst {
                ParsedInstruction::Push(v) => {
                    let compiled_val = self.compile_value(scope, v)?;
                    Instruction::Push(compiled_val)
                }
                // The three that name a depth. None of them survives into the
                // ISA: each expands into frames around the same movement one
                // step shallower. See [`Compiler::reach`].
                ParsedInstruction::Drop(d) => {
                    compiled.extend(self.reach(Reach::Discard, d));
                    continue;
                }
                ParsedInstruction::Pick(d) => {
                    compiled.extend(self.reach(Reach::Copy, d));
                    continue;
                }
                ParsedInstruction::Roll(d) => {
                    compiled.extend(self.reach(Reach::Move, d));
                    continue;
                }
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
                ParsedInstruction::Tuple(n) => Instruction::Tuple(n),
                ParsedInstruction::Untuple(n) => Instruction::Untuple(n),
                ParsedInstruction::And => Instruction::And,
                ParsedInstruction::Or => Instruction::Or,
                ParsedInstruction::ConstStringLen => Instruction::ConstStringLen,
                ParsedInstruction::ConstStringCharAt => Instruction::ConstStringCharAt,
                ParsedInstruction::IsInt => Instruction::IsInt,
                ParsedInstruction::IsBool => Instruction::IsBool,
                ParsedInstruction::IsConstString => Instruction::IsConstString,
                ParsedInstruction::IsSymbol => Instruction::IsSymbol,
                ParsedInstruction::IsTuple => Instruction::IsTuple,
                ParsedInstruction::TupleLength => Instruction::TupleLength,
                ParsedInstruction::Jump(target) => {
                    let target_idx = self.resolve_target(scope, target)?;
                    Instruction::Jump(target_idx)
                }
                ParsedInstruction::Dip(depth, target) => {
                    let target_idx = self.resolve_target(scope, target)?;
                    self.frame(depth, target_idx)
                }
                ParsedInstruction::Branch(t1, t2) => {
                    let idx1 = self.resolve_target(scope, t1)?;
                    let idx2 = self.resolve_target(scope, t2)?;
                    Instruction::Branch(idx1, idx2)
                }
                // `?` takes the rest of the block with it, so it is the end
                // of this body rather than one more instruction in it.
                ParsedInstruction::Try => {
                    let tail: Vec<ParsedInstruction> = rest.by_ref().collect();
                    compiled.extend(self.compile_try(scope, tail)?);
                    return Ok(compiled);
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
                        ResolvedItem::Sentence(idx) => Instruction::Jump(idx),
                        // A path that names a value is the predicate "equal to
                        // that value", whether it is a symbol or a const string.
                        ResolvedItem::Const(val) => {
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

    /// `?`, as the branches a user could have written in its place.
    ///
    /// A result is `(value, tag)` with `tag` being `crate::prelude::ok` or
    /// `crate::prelude::err`, so the expansion takes the pair apart, asks which
    /// tag it carries, and puts the rest of the block in the arm that runs when
    /// the answer is `ok`:
    ///
    /// ```text
    /// untuple 2
    /// branch { push ok equal } { drop 0 push false }
    /// branch { ...the rest of the block... } { push err tuple 2 }
    /// ```
    ///
    /// The first branch reads the flag `untuple` leaves: a value that is not a
    /// 2-tuple is not a result, and rather than failing on it, `?` calls it an
    /// error carrying that value — which is what `untuple` handed back. That is
    /// what keeps `?` total (see `docs/totality.md`).
    ///
    /// The failure arm is left one step short: it rebuilds the error but does
    /// not yet drop whatever the block was holding underneath it, because how
    /// much that is depends on the arity of the rest of the block, which is not
    /// known until every sentence has been emitted.
    /// [`crate::arity::balance_early_returns`] finishes it.
    fn compile_try(
        &mut self,
        scope: ModuleId,
        tail: Vec<ParsedInstruction>,
    ) -> Result<Vec<Instruction>, String> {
        let ok = self.prelude_symbol(scope, "ok")?;
        let err = self.prelude_symbol(scope, "err")?;

        // The rest of the block first, so that a `?` nested inside it records
        // itself before this one does: balancing reads the arity of a rest arm,
        // and an arm with an unbalanced `?` in it does not have one yet.
        let rest = self.compile_sentence_body(scope, tail)?;
        let rest = self.push_block(rest);

        let is_ok = self.push_block(vec![Instruction::Push(ok), Instruction::Equal]);
        let not_a_result = self.push_block(vec![
            Instruction::Drop,
            Instruction::Push(Value::Bool(false)),
        ]);
        let fail = self.push_block(vec![Instruction::Push(err), Instruction::Tuple(2)]);

        self.early_returns.push(EarlyReturn {
            rest,
            fail,
            in_sentence: self.current_sentence.clone(),
        });
        Ok(vec![
            Instruction::Untuple(2),
            Instruction::Branch(is_ok, not_a_result),
            Instruction::Branch(rest, fail),
        ])
    }

    /// The tag symbols `?` compares against.
    ///
    /// Absolute, not resolved against the sentence's own module: which symbol
    /// marks an error is a property of the program rather than of the place the
    /// `?` was written. Nothing declares them for you — a program that uses `?`
    /// says what its tags are.
    fn prelude_symbol(&self, scope: ModuleId, name: &str) -> Result<Value, String> {
        let path = Path {
            segments: vec![
                PathSegment::Crate,
                PathSegment::Identifier("prelude".to_string()),
                PathSegment::Identifier(name.to_string()),
            ],
        };
        let missing = || {
            format!(
                "`?` reads the tag `crate::prelude::{}`, which this program does not \
                 declare; a program that uses `?` needs `mod prelude {{ symbol ok symbol err }}`",
                name
            )
        };
        match self.tree.resolve(scope, &path).map_err(|_| missing())? {
            ResolvedItem::Const(val) => Ok(val),
            ResolvedItem::Sentence(_) => Err(format!(
                "`crate::prelude::{}` names a sentence, but `?` compares against it as a value",
                name
            )),
        }
    }

    /// What `pick d`, `roll d` or `drop d` becomes: one recursion, three ways.
    ///
    /// Each of the three reaches past the top value with a frame and does the
    /// same thing one shallower inside it. They part at the bottom, where there
    /// is nothing left to reach past:
    ///
    /// ```text
    /// drop 0 = drop            pick 0 = copy               roll 0 = ε
    /// drop d = dip { drop (d-1) }
    /// pick d = dip { pick (d-1) } ; swap
    /// roll d = dip { roll (d-1) } ; swap
    /// ```
    ///
    /// The trailing `swap` is what brings the answer up from under the value
    /// the frame hid, and `drop` has none because it leaves nothing to bring.
    /// `roll 1` needs no frame at all — reaching past one value to fetch the
    /// one beneath it *is* the exchange — so it is the one case written
    /// directly rather than through the recursion, which would otherwise call a
    /// block containing nothing.
    fn reach(&mut self, kind: Reach, depth: usize) -> Vec<Instruction> {
        match (kind, depth) {
            (Reach::Discard, 0) => vec![Instruction::Drop],
            (Reach::Copy, 0) => vec![Instruction::Copy],
            (Reach::Move, 0) => Vec::new(),
            (Reach::Move, 1) => vec![Instruction::Swap],
            (kind, depth) => {
                let inner = self.reach_block(kind, depth - 1);
                match kind {
                    Reach::Discard => vec![Instruction::Dip(inner)],
                    _ => vec![Instruction::Dip(inner), Instruction::Swap],
                }
            }
        }
    }

    /// The same expansion, filed as a block and shared with every other site
    /// that asks for that reach at that depth.
    fn reach_block(&mut self, kind: Reach, depth: usize) -> SentenceIndex {
        if let Some(idx) = self.reaches.get(&(kind, depth)) {
            return *idx;
        }
        let body = self.reach(kind, depth);
        let idx = self.push_block(body);
        self.reaches.insert((kind, depth), idx);
        idx
    }

    /// A call under `depth` hidden values, as that many one-deep frames.
    ///
    /// `dip 0` hides nothing and is a plain `jump`; `dip 1` is the frame
    /// itself; anything deeper is a frame around a shallower one. Nesting is
    /// the whole of what a width used to say, and the chain is shared per
    /// (depth, target) so that a sentence dipped to twice is wrapped once.
    fn frame(&mut self, depth: usize, target: SentenceIndex) -> Instruction {
        match depth {
            0 => Instruction::Jump(target),
            1 => Instruction::Dip(target),
            _ => {
                if let Some(idx) = self.frames.get(&(depth, target)) {
                    return Instruction::Dip(*idx);
                }
                let inner = self.frame(depth - 1, target);
                let idx = self.push_block(vec![inner]);
                self.frames.insert((depth, target), idx);
                Instruction::Dip(idx)
            }
        }
    }

    /// Files a compiled body as a block: a sentence nothing can name.
    ///
    /// The same thing `resolve_target` does for a `{ ... }` written in source,
    /// for bodies this compiler builds itself.
    fn push_block(&mut self, body: Vec<Instruction>) -> SentenceIndex {
        let idx = SentenceIndex::from(self.sentences.len());
        self.sentences.push(body);
        self.names.push("<inline>".to_string());
        self.annotations.push(Vec::new());
        idx
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
                    ResolvedItem::Const(_) => Err(format!(
                        "Expected sentence, found a value at path {:?}",
                        path
                    )),
                }
            }
            Target::Inline(parsed_sentence) => {
                let new_idx = SentenceIndex::from(self.sentences.len());
                self.sentences.push(Vec::new());
                self.names.push("<inline>".to_string());

                // A branch arm or dip body carries no annotations of its own:
                // it is part of the sentence that wrote it, and every
                // annotation left is a claim about a sentence being called.
                self.annotations.push(Vec::new());

                let compiled_body =
                    self.compile_sentence_body(scope, parsed_sentence.instructions)?;
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
        identities,
        ..
    } = builder;

    let mut compiler = Compiler {
        tree: &tree,
        sentences: Vec::new(),
        names: Vec::new(),
        annotations: Vec::new(),
        early_returns: Vec::new(),
        current_sentence: String::new(),
        reaches: HashMap::new(),
        frames: HashMap::new(),
    };

    // Pre-allocate space for all named sentences
    compiler.sentences.resize(sentence_counter, Vec::new());
    compiler.names.resize(sentence_counter, String::new());
    compiler.annotations.resize(sentence_counter, Vec::new());

    // Compile instructions recursively
    for (idx, (scope, sentence)) in flat_sentences.into_iter().enumerate() {
        let name = tree.fq_name(scope, &sentence.name);
        compiler.current_sentence = name.clone();
        compiler.annotations[idx] = compiler
            .resolve_annotations(scope, &sentence.annotations)
            .map_err(|e| format!("In '{}': {}", name, e))?;
        let compiled_instructions =
            compiler.compile_sentence_body(scope, sentence.body.instructions)?;
        compiler.sentences[idx] = compiled_instructions;
        compiler.names[idx] = name;
    }

    let early_returns = compiler.early_returns;

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
    library.identities = identities.into();

    crate::arity::balance_early_returns(&mut library, &early_returns)?;
    crate::arity::check_arities(&mut library)?;
    crate::arity::check_identities(&library)?;

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
        let toks = spans("// leading\n\n  push  -35\n");
        let slices: Vec<&str> = toks.iter().map(|(_, s)| *s).collect();
        assert_eq!(slices, vec!["push", "-35"]);
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

    // -----------------------------------------------------------------------
    // `identity`
    // -----------------------------------------------------------------------

    /// Assembles `input`, returning the rendered error a user would see.
    fn assemble_error(input: &str) -> String {
        let mut map = SourceMap::new();
        let file = map.add("main.hana", input.to_string());
        let err = assemble_source(&mut map, file, None).expect_err("expected an error");
        map.render(&err)
    }

    #[test]
    fn an_identity_states_two_bodies() {
        let lib = assemble("identity testing_a_test { is_bool is_bool } = { drop 0 push true };")
            .expect("should assemble");
        assert_eq!(lib.identities.len(), 1);
        let id = &lib.identities[IdentityIndex::from(0)];
        assert_eq!(id.name, "testing_a_test");
        assert_eq!(lib.sentences[id.lhs].len(), 2);
        assert_eq!(lib.sentences[id.rhs].len(), 2);
    }

    /// Each side of a claim is reachable by the name phase 4 gave it, so a tool
    /// outside the compiler can address one without knowing how the identity
    /// was declared.
    #[test]
    fn an_identity_names_both_of_its_sides() {
        let lib = assemble("mod m { identity foo { drop 0 } = { drop 0 }; }").expect("assembles");
        let names: Vec<&str> = lib.names.iter().map(|s| s.as_str()).collect();
        assert!(names.contains(&"m::foo::lhs"), "{:?}", names);
        assert!(names.contains(&"m::foo::rhs"), "{:?}", names);
    }

    /// Not in the module tree, though, so nothing can call one.
    #[test]
    fn a_path_that_names_an_identity_is_not_a_jump_target() {
        let err = assemble("identity foo { drop 0 } = { drop 0 };\nsentence a { jump foo }")
            .expect_err("expected an error");
        assert!(err.contains("names an identity"), "{}", err);
    }

    #[test]
    fn an_identity_shares_the_namespace_with_sentences() {
        let err = assemble("sentence foo { }\nidentity foo { drop 0 } = { drop 0 };")
            .expect_err("expected an error");
        assert!(err.contains("Duplicate declaration"), "{}", err);
    }

    #[test]
    fn an_identity_carries_its_annotations_onto_both_sides() {
        let lib = assemble("#[arity(1, 1)] identity foo { } = { };").expect("assembles");
        let id = &lib.identities[IdentityIndex::from(0)];
        assert!(lib.annotations[id.lhs].contains(&Annotation::Arity(1, 1)));
        assert!(lib.annotations[id.rhs].contains(&Annotation::Arity(1, 1)));
    }

    #[test]
    fn an_identity_that_leaves_a_different_amount_is_refused() {
        let rendered = assemble_error("identity mismatched { push 1 } = { };");
        assert!(
            rendered.contains("leave the stack differently"),
            "{}",
            rendered
        );
        // Spanned at the name, which is the only span an AST node carries.
        assert!(rendered.contains("^^^^^^^^^^"), "{}", rendered);
    }

    /// Net change, not full arity — and that is what the interesting laws need.
    /// `pick 1 ; drop` = nothing is `(2 -> 2)` against `(0 -> 0)`: both leave
    /// the stack as they found it, but the left needs a value to look at.
    /// Refusing this would refuse every counit and every annihilation.
    #[test]
    fn sides_may_need_different_amounts_so_long_as_they_leave_the_same() {
        assemble("identity counit { pick 1 drop 0 } = { };").expect("assembles");
    }

    #[test]
    fn an_identity_refuses_an_annotation_nothing_would_read() {
        for (ann, word) in [
            ("#[precondition(p)]", "precondition"),
            ("#[postcondition(p)]", "postcondition"),
        ] {
            let rendered = error_for(&format!("{} identity x {{ }} = {{ }};", ann));
            assert!(
                rendered.contains(&format!("`#[{}]` is not an identity annotation", word)),
                "{}",
                rendered
            );
        }
    }

    #[test]
    fn an_identity_takes_no_export_or_test_marker() {
        let rendered = error_for("export identity x { } = { };");
        assert!(
            rendered.contains("an identity takes no `export` or `test` marker"),
            "{}",
            rendered
        );
        assert!(rendered.contains("nothing calls it"), "{}", rendered);
    }

    #[test]
    fn an_identity_without_the_equals_sign_points_at_what_came_instead() {
        let rendered = error_for("identity x { drop 0 } { drop 0 };");
        assert!(rendered.contains("expected `=`, found `{`"), "{}", rendered);
    }

    /// `identity` is a hard keyword, so a body that writes one is refused by
    /// name rather than reported as a mysterious parse failure.
    #[test]
    fn identity_is_not_an_instruction() {
        let rendered = error_for("sentence a { identity }");
        assert!(
            rendered.contains("expected an instruction, found `identity`"),
            "{}",
            rendered
        );
    }

    /// The one thing the span is carried for: an identity has to know which
    /// file stated it, so a tool outside the compiler can address it per file.
    #[test]
    fn an_identity_records_the_file_it_was_stated_in() {
        let dir = std::env::temp_dir().join("hanoi_identity_file_test");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let main = dir.join("main.hana");
        std::fs::write(
            &main,
            "identity here { drop 0 } = { drop 0 };\nmod helper;\n",
        )
        .unwrap();
        std::fs::write(
            dir.join("helper.hana"),
            "identity there { drop 0 } = { drop 0 };\n",
        )
        .unwrap();

        let mut map = SourceMap::new();
        let root = map.add_path(&main, std::fs::read_to_string(&main).unwrap());
        let lib = assemble_source(&mut map, root, main.parent()).expect("assembles");

        assert_eq!(lib.identities.len(), 2);
        let here = &lib.identities[IdentityIndex::from(0)];
        let there = &lib.identities[IdentityIndex::from(1)];
        assert_ne!(here.span.file, there.span.file);
        assert_eq!(lib.identities_in(here.span.file).len(), 1);
        assert_eq!(
            map.path(there.span.file).map(|p| p.file_name().unwrap()),
            Some(std::ffi::OsStr::new("helper.hana"))
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn an_identity_answers_to_an_unambiguous_suffix() {
        let lib = assemble("mod m { identity foo { drop 0 } = { drop 0 }; }").expect("assembles");
        assert_eq!(lib.identity_by_name("foo"), Ok(IdentityIndex::from(0)));
        assert_eq!(lib.identity_by_name("m::foo"), Ok(IdentityIndex::from(0)));
        assert!(lib.identity_by_name("nope").is_err());
    }
}
