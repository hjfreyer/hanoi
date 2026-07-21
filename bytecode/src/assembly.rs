use std::collections::HashMap;
use crate::library::{Library, SentenceIndex};
use crate::opcode::Instruction;
use crate::value::{Value, Symbol, ValueSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathSegment {
    Crate,
    Super,
    Identifier(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path {
    pub segments: Vec<PathSegment>,
}

/// Token types for the assembly lexer.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Export,
    SymbolKeyword,
    TestKeyword,
    ModKeyword,
    DoubleColon,
    Semicolon,
    Identifier(String),
    StringLiteral(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    Comma,
    Colon,
    Int(i64),
    Float(f64),
    Bool(bool),
}

/// Tokenizer split logic.
fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    let mut line = 1;

    while let Some(&c) = chars.peek() {
        match c {
            '\n' => {
                line += 1;
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '#' => {
                // Comment, consume until end of line
                chars.next();
                while let Some(&next_c) = chars.peek() {
                    if next_c == '\n' {
                        break;
                    }
                    chars.next();
                }
            }
            '{' => {
                tokens.push(Token::LBrace);
                chars.next();
            }
            '}' => {
                tokens.push(Token::RBrace);
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RParen);
                chars.next();
            }
            ',' => {
                tokens.push(Token::Comma);
                chars.next();
            }
            ';' => {
                tokens.push(Token::Semicolon);
                chars.next();
            }
            ':' => {
                chars.next();
                if chars.peek() == Some(&':') {
                    chars.next();
                    tokens.push(Token::DoubleColon);
                } else {
                    tokens.push(Token::Colon);
                }
            }
            '"' => {
                chars.next(); // consume '"'
                let mut string_val = String::new();
                let mut closed = false;
                while let Some(next_c) = chars.next() {
                    if next_c == '"' {
                        closed = true;
                        break;
                    }
                    string_val.push(next_c);
                }
                if !closed {
                    return Err(format!("Line {}: Unclosed string literal", line));
                }
                tokens.push(Token::StringLiteral(string_val));
            }
            // Parse negative or positive numbers
            '-' | '0'..='9' => {
                let mut number_str = String::new();
                if c == '-' {
                    number_str.push(chars.next().unwrap());
                }

                while let Some(&next_c) = chars.peek() {
                    if next_c.is_ascii_digit() {
                        number_str.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                let mut is_float = false;
                if let Some(&'.') = chars.peek() {
                    chars.next(); // consume '.'
                    number_str.push('.');
                    is_float = true;

                    while let Some(&next_c) = chars.peek() {
                        if next_c.is_ascii_digit() {
                            number_str.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                }

                if is_float {
                    let val = number_str.parse::<f64>()
                        .map_err(|e| format!("Line {}: Invalid float '{}': {}", line, number_str, e))?;
                    tokens.push(Token::Float(val));
                } else {
                    if number_str == "-" {
                        return Err(format!("Line {}: Minus sign without digits", line));
                    }
                    let val = number_str.parse::<i64>()
                        .map_err(|e| format!("Line {}: Invalid integer '{}': {}", line, number_str, e))?;
                    tokens.push(Token::Int(val));
                }
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut ident = String::new();
                while let Some(&next_c) = chars.peek() {
                    if next_c.is_ascii_alphanumeric() || next_c == '_' {
                        ident.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                match ident.as_str() {
                    "export" => tokens.push(Token::Export),
                    "symbol" => tokens.push(Token::SymbolKeyword),
                    "test" => tokens.push(Token::TestKeyword),
                    "mod" => tokens.push(Token::ModKeyword),
                    "true" => tokens.push(Token::Bool(true)),
                    "false" => tokens.push(Token::Bool(false)),
                    _ => tokens.push(Token::Identifier(ident)),
                }
            }
            other => {
                return Err(format!("Line {}: Unexpected character '{}'", line, other));
            }
        }
    }

    Ok(tokens)
}

struct TokenStream {
    tokens: Vec<Token>,
    position: usize,
}

impl TokenStream {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn next(&mut self) -> Option<Token> {
        if self.position < self.tokens.len() {
            let t = self.tokens[self.position].clone();
            self.position += 1;
            Some(t)
        } else {
            None
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), String> {
        match self.next() {
            Some(t) if t == expected => Ok(()),
            Some(other) => Err(format!("Expected {:?}, found {:?}", expected, other)),
            None => Err(format!("Expected {:?}, found end of input", expected)),
        }
    }
}

/// Parses values into ParsedValue AST nodes.
fn parse_value(stream: &mut TokenStream) -> Result<ParsedValue, String> {
    match stream.next() {
        Some(Token::Bool(b)) => Ok(ParsedValue::Bool(b)),
        Some(Token::Int(i)) => Ok(ParsedValue::Int(i)),
        Some(Token::Float(f)) => Ok(ParsedValue::Float(f)),
        Some(Token::Identifier(name)) => {
            match name.as_str() {
                "empty_set" => {
                    if let Some(&Token::DoubleColon) = stream.peek() {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    } else {
                        Ok(ParsedValue::SetEmpty)
                    }
                }
                "universal_set" => {
                    if let Some(&Token::DoubleColon) = stream.peek() {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    } else {
                        Ok(ParsedValue::SetUniversal)
                    }
                }
                "singleton" => {
                    if stream.peek() == Some(&Token::LParen) {
                        stream.expect(Token::LParen)?;
                        let val = parse_value(stream)?;
                        stream.expect(Token::RParen)?;
                        Ok(ParsedValue::SetSingleton(Box::new(val)))
                    } else {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    }
                }
                "union" => {
                    if stream.peek() == Some(&Token::LParen) {
                        stream.expect(Token::LParen)?;
                        let left = parse_value(stream)?;
                        stream.expect(Token::Comma)?;
                        let right = parse_value(stream)?;
                        stream.expect(Token::RParen)?;
                        Ok(ParsedValue::SetUnion(Box::new(left), Box::new(right)))
                    } else {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    }
                }
                "intersection" => {
                    if stream.peek() == Some(&Token::LParen) {
                        stream.expect(Token::LParen)?;
                        let left = parse_value(stream)?;
                        stream.expect(Token::Comma)?;
                        let right = parse_value(stream)?;
                        stream.expect(Token::RParen)?;
                        Ok(ParsedValue::SetIntersection(Box::new(left), Box::new(right)))
                    } else {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    }
                }
                "difference" => {
                    if stream.peek() == Some(&Token::LParen) {
                        stream.expect(Token::LParen)?;
                        let left = parse_value(stream)?;
                        stream.expect(Token::Comma)?;
                        let right = parse_value(stream)?;
                        stream.expect(Token::RParen)?;
                        Ok(ParsedValue::SetDifference(Box::new(left), Box::new(right)))
                    } else {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    }
                }
                "complement" => {
                    if stream.peek() == Some(&Token::LParen) {
                        stream.expect(Token::LParen)?;
                        let val = parse_value(stream)?;
                        stream.expect(Token::RParen)?;
                        Ok(ParsedValue::SetComplement(Box::new(val)))
                    } else {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    }
                }
                "set_tuple" => {
                    if stream.peek() == Some(&Token::LParen) {
                        stream.expect(Token::LParen)?;
                        let mut elements = Vec::new();
                        if stream.peek() == Some(&Token::RParen) {
                            stream.next(); // consume ')'
                        } else {
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
                                    other => {
                                        return Err(format!("Expected ',' or ')', found {:?}", other));
                                    }
                                }
                            }
                        }
                        Ok(ParsedValue::SetTuple(elements))
                    } else {
                        let path = parse_path(stream, name)?;
                        Ok(ParsedValue::SymbolRef(path))
                    }
                }
                _ => {
                    let path = parse_path(stream, name)?;
                    Ok(ParsedValue::SymbolRef(path))
                }
            }
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
                    other => {
                        return Err(format!("Expected ',' or ')', found {:?}", other));
                    }
                }
            }
            Ok(ParsedValue::Tuple(elements))
        }
        Some(other) => Err(format!("Expected value, found {:?}", other)),
        None => Err("Expected value, found end of input".to_string()),
    }
}

fn parse_path(stream: &mut TokenStream, first_ident: String) -> Result<Path, String> {
    let mut segments = vec![parse_segment(&first_ident)];
    while let Some(&Token::DoubleColon) = stream.peek() {
        stream.next(); // consume '::'
        match stream.next() {
            Some(Token::Identifier(name)) => {
                segments.push(parse_segment(&name));
            }
            Some(other) => return Err(format!("Expected identifier after '::', found {:?}", other)),
            None => return Err("Expected identifier after '::', found end of input".to_string()),
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

/// Parses a target which is either a named label or an inline `{}` block.
fn parse_target(stream: &mut TokenStream) -> Result<Target, String> {
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
        other => Err(format!("Expected label target or inline block '{{', found {:?}", other)),
    }
}

fn parse_sentence_body(stream: &mut TokenStream) -> Result<ParsedSentence, String> {
    stream.expect(Token::LBrace)?;
    let mut instructions = Vec::new();

    while stream.peek() != Some(&Token::RBrace) && stream.peek().is_some() {
        let inst = parse_instruction(stream)?;
        instructions.push(inst);
    }

    stream.expect(Token::RBrace)?;
    Ok(ParsedSentence { instructions })
}

fn parse_usize(stream: &mut TokenStream) -> Result<usize, String> {
    match stream.next() {
        Some(Token::Int(val)) if val >= 0 => Ok(val as usize),
        Some(other) => Err(format!("Expected non-negative integer, found {:?}", other)),
        None => Err("Expected non-negative integer, found end of input".to_string()),
    }
}

fn parse_instruction(stream: &mut TokenStream) -> Result<ParsedInstruction, String> {
    let token = stream.next().ok_or_else(|| "Expected instruction, found end of input".to_string())?;
    let name = match token {
        Token::Identifier(name) => name,
        Token::ModKeyword => "mod".to_string(),
        other => return Err(format!("Expected instruction mnemonic, found {:?}", other)),
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
        "print" => Ok(ParsedInstruction::Print),
        "jump" => {
            let target = parse_target(stream)?;
            Ok(ParsedInstruction::Jump(target))
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
        "set_contains" => Ok(ParsedInstruction::SetContains),
        "set_union" => Ok(ParsedInstruction::SetUnion),
        "set_intersection" => Ok(ParsedInstruction::SetIntersection),
        "set_difference" => Ok(ParsedInstruction::SetDifference),
        "set_complement" => Ok(ParsedInstruction::SetComplement),
        "set_singleton" => Ok(ParsedInstruction::SetSingleton),
        "set_tuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::SetTuple(size))
        }
        "set_choose" => Ok(ParsedInstruction::SetChoose),
        "symbol_len" => Ok(ParsedInstruction::SymbolLen),
        "symbol_char_at" => Ok(ParsedInstruction::SymbolCharAt),
        other => Err(format!("Unknown instruction mnemonic: '{}'", other)),
    }
}

enum TopLevelItem {
    SymbolDecl {
        name: String,
        debug_desc: Option<String>,
    },
    Sentence(TopLevelSentence),
    Mod {
        name: String,
        items: Vec<TopLevelItem>,
    },
    Compose {
        name: String,
        composer: String,
        args: Vec<Path>,
    },
}

struct TopLevelSentence {
    is_exported: bool,
    is_test: bool,
    name: String,
    body: ParsedSentence,
}

fn parse_top_level(stream: &mut TokenStream, base_dir: Option<&std::path::Path>) -> Result<Vec<TopLevelItem>, String> {
    parse_items(stream, None, base_dir)
}

fn parse_items(stream: &mut TokenStream, end_token: Option<Token>, base_dir: Option<&std::path::Path>) -> Result<Vec<TopLevelItem>, String> {
    let mut items = Vec::new();

    while stream.peek().is_some() {
        if let Some(ref end) = end_token {
            if stream.peek() == Some(end) {
                break;
            }
        }

        if stream.peek() == Some(&Token::SymbolKeyword) {
            stream.next(); // consume 'symbol'
            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected symbol name identifier, found {:?}", other)),
                None => return Err("Expected symbol name identifier, found end of input".to_string()),
            };

            let debug_desc = if let Some(Token::StringLiteral(_)) = stream.peek() {
                if let Some(Token::StringLiteral(desc)) = stream.next() {
                    Some(desc)
                } else {
                    None
                }
            } else {
                None
            };

            items.push(TopLevelItem::SymbolDecl { name, debug_desc });
        } else if stream.peek() == Some(&Token::ModKeyword) {
            stream.next(); // consume 'mod'
            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected module name identifier, found {:?}", other)),
                None => return Err("Expected module name identifier, found end of input".to_string()),
            };
            
            if let Some(&Token::Identifier(ref ident)) = stream.peek() {
                if ident == "compose_concurrent" || ident == "compose_hidden" || ident == "compose_prefix" {
                    let composer = match stream.next() {
                        Some(Token::Identifier(id)) => id,
                        _ => unreachable!(),
                    };
                    stream.expect(Token::LParen)?;
                    let mut args = Vec::new();
                    if stream.peek() != Some(&Token::RParen) {
                        loop {
                            let first_ident = match stream.next() {
                                Some(Token::Identifier(id)) => id,
                                Some(other) => return Err(format!("Expected identifier for path, found {:?}", other)),
                                None => return Err("Expected identifier for path, found end of input".to_string()),
                            };
                            args.push(parse_path(stream, first_ident)?);
                            if stream.peek() == Some(&Token::Comma) {
                                stream.next();
                            } else {
                                break;
                            }
                        }
                    }
                    stream.expect(Token::RParen)?;
                    stream.expect(Token::Semicolon)?;
                    items.push(TopLevelItem::Compose { name, composer, args });
                    continue;
                }
            }
            
            if stream.peek() == Some(&Token::Semicolon) {
                stream.next(); // consume ';'
                let base = base_dir.ok_or_else(|| {
                    format!("Cannot load external module '{}' because no base directory context was provided", name)
                })?;
                let file_name = format!("{}.hana", name);
                let file_path = base.join(&file_name);
                let file_content = std::fs::read_to_string(&file_path)
                    .map_err(|e| format!("Failed to read module file '{}' at {:?}: {}", file_name, file_path, e))?;
                
                let tokens = tokenize(&file_content)?;
                let mut sub_stream = TokenStream { tokens, position: 0 };
                let new_base = base.join(&name);
                let mod_items = parse_items(&mut sub_stream, None, Some(&new_base))?;
                items.push(TopLevelItem::Mod { name, items: mod_items });
            } else {
                stream.expect(Token::LBrace)?;
                let new_base = base_dir.map(|b| b.join(&name));
                let mod_items = parse_items(stream, Some(Token::RBrace), new_base.as_deref())?;
                stream.expect(Token::RBrace)?;
                items.push(TopLevelItem::Mod { name, items: mod_items });
            }
        } else {
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

            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected sentence name identifier, found {:?}", other)),
                None => return Err("Expected sentence name identifier, found end of input".to_string()),
            };

            if stream.peek() == Some(&Token::Colon) {
                stream.next();
            }

            let body = parse_sentence_body(stream)?;

            items.push(TopLevelItem::Sentence(TopLevelSentence {
                is_exported,
                is_test,
                name,
                body,
            }));
        }
    }

    Ok(items)
}

#[derive(Debug, Clone)]
enum ParsedValue {
    Bool(bool),
    Int(i64),
    Float(f64),
    Tuple(Vec<ParsedValue>),
    SymbolRef(Path),
    SetEmpty,
    SetUniversal,
    SetSingleton(Box<ParsedValue>),
    SetUnion(Box<ParsedValue>, Box<ParsedValue>),
    SetIntersection(Box<ParsedValue>, Box<ParsedValue>),
    SetDifference(Box<ParsedValue>, Box<ParsedValue>),
    SetComplement(Box<ParsedValue>),
    SetTuple(Vec<ParsedValue>),
}

struct ParsedSentence {
    instructions: Vec<ParsedInstruction>,
}

enum Target {
    Label(Path),
    Inline(ParsedSentence),
}

enum ParsedInstruction {
    Push(ParsedValue),
    Drop(usize),
    Pick(usize),
    Roll(usize),
    Equal,
    Greater,
    Less,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Not,
    Negate,
    Print,
    Jump(Target),
    Branch(Target, Target),
    Panic,
    Assert,
    AssertEqual,
    Tuple(usize),
    Untuple(usize),
    And,
    Or,
    SetContains,
    SetUnion,
    SetIntersection,
    SetDifference,
    SetComplement,
    SetSingleton,
    SetTuple(usize),
    SetChoose,
    SymbolLen,
    SymbolCharAt,
}

/// The result of parsing and compiling assembly code.
#[derive(Debug, Clone, PartialEq)]
pub struct AssemblyResult {
    /// The compiled bytecode library.
    pub library: Library,
    /// Maps exported sentence label names to their SentenceIndex.
    pub exports: HashMap<String, SentenceIndex>,
    /// Maps test sentence label names to their SentenceIndex.
    pub tests: HashMap<String, SentenceIndex>,
}

struct Module {
    name: String,
    symbols: HashMap<String, Value>,
    sentences: HashMap<String, SentenceIndex>,
    submodules: HashMap<String, Module>,
}

impl Module {
    fn new(name: String) -> Self {
        Self {
            name,
            symbols: HashMap::new(),
            sentences: HashMap::new(),
            submodules: HashMap::new(),
        }
    }
}

fn build_module_tree(
    items: Vec<TopLevelItem>,
    current_path: &mut Vec<String>,
    symbol_counter: &mut usize,
    sentence_counter: &mut usize,
    module: &mut Module,
    flat_sentences: &mut Vec<(Vec<String>, TopLevelSentence)>,
    exports: &mut HashMap<String, SentenceIndex>,
    tests: &mut HashMap<String, SentenceIndex>,
) -> Result<(), String> {
    for item in items {
        match item {
            TopLevelItem::SymbolDecl { name, debug_desc } => {
                if name == "crate" || name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", name));
                }

                if module.symbols.contains_key(&name)
                    || module.sentences.contains_key(&name)
                    || module.submodules.contains_key(&name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", name, module.name));
                }

                let fq_name = if current_path.is_empty() {
                    name.clone()
                } else {
                    format!("{}::{}", current_path.join("::"), name)
                };

                let desc = debug_desc.unwrap_or(fq_name);
                let symbol = Value::Symbol(Symbol {
                    id: *symbol_counter,
                    name: desc,
                });
                *symbol_counter += 1;

                module.symbols.insert(name, symbol);
            }
            TopLevelItem::Sentence(s) => {
                if s.name == "crate" || s.name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", s.name));
                }

                if module.symbols.contains_key(&s.name)
                    || module.sentences.contains_key(&s.name)
                    || module.submodules.contains_key(&s.name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", s.name, module.name));
                }

                let s_idx = SentenceIndex::from(*sentence_counter);
                *sentence_counter += 1;

                module.sentences.insert(s.name.clone(), s_idx);

                let fq_name = if current_path.is_empty() {
                    s.name.clone()
                } else {
                    format!("{}::{}", current_path.join("::"), s.name)
                };

                if s.is_exported {
                    exports.insert(fq_name.clone(), s_idx);
                }
                if s.is_test {
                    tests.insert(fq_name.clone(), s_idx);
                }

                flat_sentences.push((current_path.clone(), s));
            }
            TopLevelItem::Mod { name, items: mod_items } => {
                if name == "crate" || name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", name));
                }

                if module.symbols.contains_key(&name)
                    || module.sentences.contains_key(&name)
                    || module.submodules.contains_key(&name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", name, module.name));
                }

                let mut submodule = Module::new(name.clone());
                current_path.push(name.clone());
                build_module_tree(
                    mod_items,
                    current_path,
                    symbol_counter,
                    sentence_counter,
                    &mut submodule,
                    flat_sentences,
                    exports,
                    tests,
                )?;
                current_path.pop();

                module.submodules.insert(name, submodule);
            }
            TopLevelItem::Compose { name, composer, args } => {
                if name == "crate" || name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", name));
                }

                if module.symbols.contains_key(&name)
                    || module.sentences.contains_key(&name)
                    || module.submodules.contains_key(&name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", name, module.name));
                }

                let generated_items = generate_composition_items(&composer, &args)?;
                let mut submodule = Module::new(name.clone());
                current_path.push(name.clone());
                build_module_tree(
                    generated_items,
                    current_path,
                    symbol_counter,
                    sentence_counter,
                    &mut submodule,
                    flat_sentences,
                    exports,
                    tests,
                )?;
                current_path.pop();

                module.submodules.insert(name, submodule);
            }
        }
    }
    Ok(())
}

fn adjust_path(path: &Path) -> Path {
    let mut segments = Vec::new();
    if let Some(first) = path.segments.first() {
        match first {
            PathSegment::Crate => segments = path.segments.clone(),
            _ => {
                segments.push(PathSegment::Super);
                segments.extend(path.segments.clone());
            }
        }
    }
    Path { segments }
}

fn compose_concurrent(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 3 {
        return Err("compose_concurrent requires exactly 3 arguments".to_string());
    }
    let p1 = adjust_path(&args[0]);
    let p2 = adjust_path(&args[1]);
    let sync_fn = adjust_path(&args[2]);

    let mut p1_init = p1.clone(); p1_init.segments.push(PathSegment::Identifier("init".to_string()));
    let mut p2_init = p2.clone(); p2_init.segments.push(PathSegment::Identifier("init".to_string()));
    let mut p1_accept = p1.clone(); p1_accept.segments.push(PathSegment::Identifier("accept".to_string()));
    let mut p2_accept = p2.clone(); p2_accept.segments.push(PathSegment::Identifier("accept".to_string()));
    let mut p1_emit = p1.clone(); p1_emit.segments.push(PathSegment::Identifier("emit".to_string()));
    let mut p2_emit = p2.clone(); p2_emit.segments.push(PathSegment::Identifier("emit".to_string()));
    let mut p1_process = p1.clone(); p1_process.segments.push(PathSegment::Identifier("process".to_string()));
    let mut p2_process = p2.clone(); p2_process.segments.push(PathSegment::Identifier("process".to_string()));

    let init_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "init".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Initialize both component states
                ParsedInstruction::Jump(Target::Label(p1_init)),
                ParsedInstruction::Jump(Target::Label(p2_init)),
                // Package them as a tuple (state1, state2)
                ParsedInstruction::Tuple(2),
            ],
        },
    };

    let accept_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "accept".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Extract component states from the joint tuple
                // Stack: [joint_state] -> [joint_state, joint_state]
                ParsedInstruction::Pick(0),
                // Stack: [joint_state, joint_state] -> [joint_state, C_state, B_state]
                ParsedInstruction::Untuple(2),
                // Stack: [joint_state, C_state, B_state] -> [joint_state, B_state, C_state]
                ParsedInstruction::Roll(1),
                
                // Invoke P1's accept function
                // Stack: [joint_state, B_state, C_state] -> [joint_state, B_state, C_state, C_accept]
                ParsedInstruction::Jump(Target::Label(p1_accept.clone())),
                // Discard C_state
                // Stack: [joint_state, B_state, C_state, C_accept] -> [joint_state, B_state, C_accept]
                ParsedInstruction::Drop(1),
                // Swap B_state and C_accept
                // Stack: [joint_state, B_state, C_accept] -> [joint_state, C_accept, B_state]
                ParsedInstruction::Roll(1),
                
                // Invoke P2's accept function
                // Stack: [joint_state, C_accept, B_state] -> [joint_state, C_accept, B_state, B_accept]
                ParsedInstruction::Jump(Target::Label(p2_accept.clone())),
                // Discard B_state
                // Stack: [joint_state, C_accept, B_state, B_accept] -> [joint_state, C_accept, B_accept]
                ParsedInstruction::Drop(1),
                
                // Compute union(C_accept, B_accept) for asynchronous events
                // Stack: [joint_state, C_accept, B_accept] -> [joint_state, C_accept, B_accept, C_accept]
                ParsedInstruction::Pick(1),
                // Stack: -> [joint_state, C_accept, B_accept, C_accept, B_accept]
                ParsedInstruction::Pick(1),
                // Stack: -> [joint_state, C_accept, B_accept, C_union_B]
                ParsedInstruction::SetUnion,
                
                // Compute AsyncAccepted = difference(C_union_B, SyncSet)
                // Stack: -> [joint_state, C_accept, B_accept, C_union_B, SyncSet]
                ParsedInstruction::Jump(Target::Label(sync_fn.clone())),
                // Stack: -> [joint_state, C_accept, B_accept, AsyncAccepted]
                ParsedInstruction::SetDifference,
                
                // Move C_accept and B_accept to top to intersect them
                // Stack: -> [joint_state, B_accept, AsyncAccepted, C_accept]
                ParsedInstruction::Roll(2),
                // Stack: -> [joint_state, AsyncAccepted, C_accept, B_accept]
                ParsedInstruction::Roll(2),
                // Stack: -> [joint_state, AsyncAccepted, C_B_intersection]
                ParsedInstruction::SetIntersection,
                
                // Intersect with SyncEvents
                // Stack: -> [joint_state, AsyncAccepted, C_B_intersection, SyncSet]
                ParsedInstruction::Jump(Target::Label(sync_fn.clone())),
                // Stack: -> [joint_state, AsyncAccepted, SyncAccepted]
                ParsedInstruction::SetIntersection,
                
                // Union AsyncAccepted and SyncAccepted
                // Stack: -> [joint_state, Result]
                ParsedInstruction::SetUnion,
            ],
        },
    };

    let emit_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "emit".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Extract joint state parts: [joint_state] -> [joint_state, s1, s2]
                ParsedInstruction::Pick(0),
                ParsedInstruction::Untuple(2),
                ParsedInstruction::Roll(1), // Stack: [joint_state, s2, s1]
                
                // P1 accept and emit
                // Stack: [joint_state, s2, s1] -> [joint_state, s2, s1, A1]
                ParsedInstruction::Pick(0),
                ParsedInstruction::Jump(Target::Label(p1_accept.clone())),
                ParsedInstruction::Drop(1), // Stack: [joint_state, s2, s1, A1]
                ParsedInstruction::Roll(1), // Stack: [joint_state, s2, A1, s1]
                ParsedInstruction::Jump(Target::Label(p1_emit.clone())),
                ParsedInstruction::Drop(1), // Stack: [joint_state, s2, A1, E1]
                
                // P2 accept and emit
                // Stack: [joint_state, s2, A1, E1] -> [joint_state, A1, E1, s2]
                ParsedInstruction::Roll(2),
                // Stack: -> [joint_state, A1, E1, s2, s2] -> [joint_state, A1, E1, s2, s2, A2]
                ParsedInstruction::Pick(0),
                ParsedInstruction::Jump(Target::Label(p2_accept.clone())),
                ParsedInstruction::Drop(1), // Stack: [joint_state, A1, E1, s2, A2]
                ParsedInstruction::Roll(1), // Stack: [joint_state, A1, E1, A2, s2]
                ParsedInstruction::Jump(Target::Label(p2_emit.clone())),
                ParsedInstruction::Drop(1), // Stack: [joint_state, A1, E1, A2, E2]
                
                // P2_participate = E2 U A2
                ParsedInstruction::Pick(0),
                ParsedInstruction::Roll(2),
                ParsedInstruction::SetUnion, // Stack: [joint_state, A1, E1, E2, P2]
                
                // P1_participate = E1 U A1
                ParsedInstruction::Pick(2),
                ParsedInstruction::Roll(4),
                ParsedInstruction::SetUnion, // Stack: [joint_state, E1, E2, P2, P1]
                
                // P_both = P1_participate intersect P2_participate
                ParsedInstruction::SetIntersection, // Stack: [joint_state, E1, E2, P_both]
                
                // P_both_sync = P_both intersect SyncSet
                ParsedInstruction::Jump(Target::Label(sync_fn.clone())),
                ParsedInstruction::SetIntersection, // Stack: [joint_state, E1, E2, P_both_sync]
                
                // E_union = E1 U E2
                ParsedInstruction::Roll(2),
                ParsedInstruction::Roll(2),
                ParsedInstruction::SetUnion, // Stack: [joint_state, P_both_sync, E_union]
                
                // E_sync = E_union intersect P_both_sync
                ParsedInstruction::Pick(0),
                ParsedInstruction::Pick(2),
                ParsedInstruction::SetIntersection, // Stack: [joint_state, P_both_sync, E_union, E_sync]
                
                // E_async = E_union difference SyncSet
                ParsedInstruction::Roll(1),
                ParsedInstruction::Jump(Target::Label(sync_fn.clone())),
                ParsedInstruction::SetDifference, // Stack: [joint_state, P_both_sync, E_sync, E_async]
                
                // E_joint = E_sync U E_async
                ParsedInstruction::SetUnion, // Stack: [joint_state, P_both_sync, E_joint]
                
                // Clean up stack: drop P_both_sync, leaving joint_state underneath E_joint
                ParsedInstruction::Drop(1),
            ],
        },
    };

    let process_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "process".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Check if event is synchronized
                // Stack: [joint_state, event] -> [joint_state, event, event]
                ParsedInstruction::Pick(0),
                // Stack: -> [joint_state, event, event, SyncSet]
                ParsedInstruction::Jump(Target::Label(sync_fn.clone())),
                // Stack: -> [joint_state, event, is_synchronized]
                ParsedInstruction::SetContains,
                
                // Branch on whether the event is synchronized
                ParsedInstruction::Branch(
                    // --- SYNCHRONIZED CASE ---
                    // Both components must process the event simultaneously
                    Target::Inline(ParsedSentence {
                        instructions: vec![
                            // Swap joint_state and event
                            // Stack: [joint_state, event] -> [event, joint_state]
                            ParsedInstruction::Roll(1),
                            // Stack: -> [event, C_state, B_state]
                            ParsedInstruction::Untuple(2),
                            
                            // Copy event to top
                            // Stack: -> [event, C_state, B_state, event]
                            ParsedInstruction::Pick(2),
                            // Move C_state to top
                            // Stack: -> [event, B_state, event, C_state]
                            ParsedInstruction::Roll(2),
                            // Swap event and C_state
                            // Stack: -> [event, B_state, C_state, event]
                            ParsedInstruction::Roll(1),
                            // Process P1 transition
                            // Stack: -> [event, B_state, C_state']
                            ParsedInstruction::Jump(Target::Label(p1_process.clone())),
                            
                            // Swap C_state' and B_state
                            // Stack: -> [event, C_state', B_state]
                            ParsedInstruction::Roll(1),
                            // Move event to top
                            // Stack: -> [C_state', B_state, event]
                            ParsedInstruction::Roll(2),
                            // Process P2 transition
                            // Stack: -> [C_state', B_state']
                            ParsedInstruction::Jump(Target::Label(p2_process.clone())),
                            
                            // Wrap into next joint state tuple
                            // Stack: -> [(C_state', B_state')]
                            ParsedInstruction::Tuple(2),
                        ]
                    }),
                    // --- UNSYNCHRONIZED CASE ---
                    // Only one component processes the event asynchronously
                    Target::Inline(ParsedSentence {
                        instructions: vec![
                            // Swap joint_state and event
                            // Stack: [joint_state, event] -> [event, joint_state]
                            ParsedInstruction::Roll(1),
                            // Stack: -> [event, C_state, B_state]
                            ParsedInstruction::Untuple(2),
                            
                            // Check if P1 participates in the event
                            // Stack: -> [event, C_state, B_state, C_state]
                            ParsedInstruction::Pick(1),
                            // Stack: -> [event, C_state, B_state, C_state, C_accept]
                            ParsedInstruction::Jump(Target::Label(p1_accept.clone())),
                            // Stack: -> [event, C_state, B_state, C_accept]
                            ParsedInstruction::Drop(1),
                            // Stack: -> [event, C_state, B_state, C_accept, C_state]
                            ParsedInstruction::Pick(2),
                            // Stack: -> [event, C_state, B_state, C_accept, C_state, C_emit]
                            ParsedInstruction::Jump(Target::Label(p1_emit.clone())),
                            // Stack: -> [event, C_state, B_state, C_accept, C_emit]
                            ParsedInstruction::Drop(1),
                            // Stack: -> [event, C_state, B_state, C_participate]
                            ParsedInstruction::SetUnion,
                            // Stack: -> [event, C_state, B_state, C_participate, event]
                            ParsedInstruction::Pick(3),
                            // Stack: -> [event, C_state, B_state, event, C_participate]
                            ParsedInstruction::Roll(1),
                            // Stack: -> [event, C_state, B_state, p1_participates]
                            ParsedInstruction::SetContains,
                            
                            // Check if P2 participates in the event
                            // Stack: -> [event, C_state, B_state, p1_participates, B_state]
                            ParsedInstruction::Pick(1),
                            // Stack: -> [event, C_state, B_state, p1_participates, B_state, B_accept]
                            ParsedInstruction::Jump(Target::Label(p2_accept.clone())),
                            // Stack: -> [event, C_state, B_state, p1_participates, B_accept]
                            ParsedInstruction::Drop(1),
                            // Stack: -> [event, C_state, B_state, p1_participates, B_accept, B_state]
                            ParsedInstruction::Pick(2),
                            // Stack: -> [event, C_state, B_state, p1_participates, B_accept, B_state, B_emit]
                            ParsedInstruction::Jump(Target::Label(p2_emit.clone())),
                            // Stack: -> [event, C_state, B_state, p1_participates, B_accept, B_emit]
                            ParsedInstruction::Drop(1),
                            // Stack: -> [event, C_state, B_state, p1_participates, B_participate]
                            ParsedInstruction::SetUnion,
                            // Stack: -> [event, C_state, B_state, p1_participates, B_participate, event]
                            ParsedInstruction::Pick(4),
                            // Stack: -> [event, C_state, B_state, p1_participates, event, B_participate]
                            ParsedInstruction::Roll(1),
                            // Stack: -> [event, C_state, B_state, p1_participates, p2_participates]
                            ParsedInstruction::SetContains,
                            
                            // Swap p1_participates and p2_participates
                            // Stack: -> [event, C_state, B_state, p2_participates, p1_participates]
                            ParsedInstruction::Roll(1),
                            // Branch on p1_participates
                            ParsedInstruction::Branch(
                                // P1 accepts
                                Target::Inline(ParsedSentence {
                                    instructions: vec![
                                        // Discard p2_participates
                                        // Stack: [event, C_state, B_state]
                                        ParsedInstruction::Drop(0),
                                        
                                        // Copy event to top
                                        // Stack: -> [event, C_state, B_state, event]
                                        ParsedInstruction::Pick(2),
                                        // Move C_state to top
                                        // Stack: -> [event, B_state, event, C_state]
                                        ParsedInstruction::Roll(2),
                                        // Swap event and C_state
                                        // Stack: -> [event, B_state, C_state, event]
                                        ParsedInstruction::Roll(1),
                                        // Process P1 transition
                                        // Stack: -> [event, B_state, C_state']
                                        ParsedInstruction::Jump(Target::Label(p1_process.clone())),
                                        
                                        // Move event to top and discard it
                                        // Stack: -> [B_state, C_state', event]
                                        ParsedInstruction::Roll(2),
                                        // Stack: -> [B_state, C_state']
                                        ParsedInstruction::Drop(0),
                                        // Swap C_state' and B_state (original unchanged state)
                                        // Stack: -> [C_state', B_state]
                                        ParsedInstruction::Roll(1),
                                        // Wrap next state tuple
                                        ParsedInstruction::Tuple(2),
                                    ]
                                }),
                                // P1 does not accept; check if P2 accepts
                                Target::Inline(ParsedSentence {
                                    instructions: vec![
                                        // Branch on p2_participates
                                        // Stack: [event, C_state, B_state, p2_participates]
                                        ParsedInstruction::Branch(
                                            // P2 accepts
                                            Target::Inline(ParsedSentence {
                                                instructions: vec![
                                                    // Copy event to top
                                                    // Stack: [event, C_state, B_state] -> [event, C_state, B_state, event]
                                                    ParsedInstruction::Pick(2),
                                                    // Process P2 transition
                                                    // Stack: -> [event, C_state, B_state']
                                                    ParsedInstruction::Jump(Target::Label(p2_process.clone())),
                                                    
                                                    // Move event to top and discard it
                                                    // Stack: -> [C_state, B_state', event]
                                                    ParsedInstruction::Roll(2),
                                                    // Stack: -> [C_state, B_state']
                                                    ParsedInstruction::Drop(0),
                                                    // Wrap next state tuple
                                                    ParsedInstruction::Tuple(2),
                                                ]
                                            }),
                                            // Neither accepts: illegal transition in composition
                                            Target::Inline(ParsedSentence {
                                                instructions: vec![
                                                    ParsedInstruction::Panic,
                                                ]
                                            })
                                        )
                                    ]
                                })
                            )
                        ]
                    })
                )
            ],
        },
    };

    Ok(vec![
        TopLevelItem::Sentence(init_sentence),
        TopLevelItem::Sentence(accept_sentence),
        TopLevelItem::Sentence(emit_sentence),
        TopLevelItem::Sentence(process_sentence),
    ])
}

fn compose_hidden(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 2 {
        return Err("compose_hidden requires exactly 2 arguments".to_string());
    }
    let concurrent = adjust_path(&args[0]);
    let hidden_fn = adjust_path(&args[1]);

    let mut concurrent_init = concurrent.clone(); concurrent_init.segments.push(PathSegment::Identifier("init".to_string()));
    let mut concurrent_accept = concurrent.clone(); concurrent_accept.segments.push(PathSegment::Identifier("accept".to_string()));
    let mut concurrent_emit = concurrent.clone(); concurrent_emit.segments.push(PathSegment::Identifier("emit".to_string()));
    let mut concurrent_process = concurrent.clone(); concurrent_process.segments.push(PathSegment::Identifier("process".to_string()));

    let init_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "init".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Delegate initialization to joint concurrent system
                ParsedInstruction::Jump(Target::Label(concurrent_init)),
            ],
        },
    };

    let set_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "set".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Return the set of synchronized (hidden) events
                ParsedInstruction::Jump(Target::Label(hidden_fn.clone())),
            ],
        },
    };

    let accept_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "accept".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Query the concurrent accept set
                // Stack: [joint_state] -> [joint_state, joint_state]
                ParsedInstruction::Pick(0),
                // Stack: -> [joint_state, JointAccept]
                ParsedInstruction::Jump(Target::Label(concurrent_accept.clone())),
                // Stack: -> [joint_state, JointAccept]
                ParsedInstruction::Drop(1),
                
                // Compute NonHiddenAccepted = difference(JointAccept, SyncSet)
                // Stack: -> [joint_state, JointAccept, SyncSet]
                ParsedInstruction::Jump(Target::Label(hidden_fn.clone())),
                // Stack: -> [joint_state, NonHiddenAccepted]
                ParsedInstruction::SetDifference,
            ],
        },
    };

    let emit_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "emit".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Query concurrent emit: [joint_state] -> [joint_state, JointEmit]
                ParsedInstruction::Pick(0),
                ParsedInstruction::Jump(Target::Label(concurrent_emit.clone())),
                ParsedInstruction::Drop(1),
                
                // Compute NonHiddenEmit = JointEmit \ H
                // Stack: -> [joint_state, JointEmit, JointEmit]
                ParsedInstruction::Pick(0),
                // Stack: -> [joint_state, JointEmit, JointEmit, H]
                ParsedInstruction::Jump(Target::Label(hidden_fn.clone())),
                // Stack: -> [joint_state, JointEmit, NonHiddenEmit]
                ParsedInstruction::SetDifference,
                
                // Compute HasSync = JointEmit \cap H
                // Stack: -> [joint_state, NonHiddenEmit, JointEmit]
                ParsedInstruction::Roll(1),
                // Stack: -> [joint_state, NonHiddenEmit, JointEmit, H]
                ParsedInstruction::Jump(Target::Label(hidden_fn.clone())),
                // Stack: -> [joint_state, NonHiddenEmit, HasSync]
                ParsedInstruction::SetIntersection,
                
                // If HasSync is not empty, union with {tau}
                ParsedInstruction::Push(ParsedValue::SetEmpty),
                ParsedInstruction::Equal,
                ParsedInstruction::Branch(
                    // HasSync is empty: do nothing, returning NonHiddenEmit
                    Target::Inline(ParsedSentence {
                        instructions: vec![]
                    }),
                    // HasSync contains hidden events: union with {tau}
                    Target::Inline(ParsedSentence {
                        instructions: vec![
                            ParsedInstruction::Push(ParsedValue::SymbolRef(Path {
                                segments: vec![
                                    PathSegment::Crate,
                                    PathSegment::Identifier("prelude".to_string()),
                                    PathSegment::Identifier("event".to_string()),
                                    PathSegment::Identifier("tau".to_string()),
                                ],
                            })),
                            ParsedInstruction::SetSingleton,
                            ParsedInstruction::SetUnion,
                        ]
                    })
                ),
            ],
        },
    };

    let process_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "process".to_string(),
        body: ParsedSentence {
            instructions: vec![
                // Check if the event is a tau transition
                // Stack: [joint_state, event] -> [joint_state, event, event]
                ParsedInstruction::Pick(0),
                // Stack: -> [joint_state, event, event, tau]
                ParsedInstruction::Push(ParsedValue::SymbolRef(Path {
                    segments: vec![
                        PathSegment::Crate,
                        PathSegment::Identifier("prelude".to_string()),
                        PathSegment::Identifier("event".to_string()),
                        PathSegment::Identifier("tau".to_string()),
                    ],
                })),
                // Stack: -> [joint_state, event, is_tau]
                ParsedInstruction::Equal,
                ParsedInstruction::Branch(
                    // --- TAU CASE ---
                    // Choose a hidden event to drive internally
                    Target::Inline(ParsedSentence {
                        instructions: vec![
                            // Discard event (which is tau)
                            // Stack: [joint_state]
                            ParsedInstruction::Drop(0),
                            
                            // Fetch accepted joint events
                            // Stack: -> [joint_state, JointEmit]
                            ParsedInstruction::Jump(Target::Label(concurrent_emit.clone())),
                            // Fetch hidden events
                            // Stack: -> [joint_state, JointEmit, SyncSet]
                            ParsedInstruction::Jump(Target::Label(hidden_fn.clone())),
                            // Stack: -> [joint_state, HasSync]
                            ParsedInstruction::SetIntersection,
                            // Choose one event: returns tuple (chosen_event, has_element)
                            // Stack: -> [joint_state, has_element, chosen_event] (after untuple)
                            ParsedInstruction::SetChoose,
                            ParsedInstruction::Untuple(2),
                            ParsedInstruction::Branch(
                                // Event selected successfully; process it
                                // Stack: [joint_state, chosen_event]
                                Target::Inline(ParsedSentence {
                                    instructions: vec![
                                        ParsedInstruction::Jump(Target::Label(concurrent_process.clone())),
                                    ]
                                }),
                                // No hidden event accepts; impossible tau
                                Target::Inline(ParsedSentence {
                                    instructions: vec![
                                        ParsedInstruction::Panic,
                                    ]
                                })
                            )
                        ]
                    }),
                    // --- OBSERVABLE CASE ---
                    // Directly delegate to concurrent process transition
                    Target::Inline(ParsedSentence {
                        instructions: vec![
                            ParsedInstruction::Jump(Target::Label(concurrent_process)),
                        ]
                    })
                )
            ],
        },
    };

    Ok(vec![
        TopLevelItem::Sentence(init_sentence),
        TopLevelItem::Sentence(set_sentence),
        TopLevelItem::Sentence(accept_sentence),
        TopLevelItem::Sentence(emit_sentence),
        TopLevelItem::Sentence(process_sentence),
    ])
}

fn compose_prefix(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 2 {
        return Err("compose_prefix requires exactly 2 arguments: target_machine and prefix_symbol".to_string());
    }
    let machine = adjust_path(&args[0]);
    let prefix_sym = adjust_path(&args[1]);

    let mut machine_init = machine.clone(); machine_init.segments.push(PathSegment::Identifier("init".to_string()));
    let mut machine_accept = machine.clone(); machine_accept.segments.push(PathSegment::Identifier("accept".to_string()));
    let mut machine_emit = machine.clone(); machine_emit.segments.push(PathSegment::Identifier("emit".to_string()));
    let mut machine_process = machine.clone(); machine_process.segments.push(PathSegment::Identifier("process".to_string()));

    let init_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "init".to_string(),
        body: ParsedSentence {
            instructions: vec![
                ParsedInstruction::Jump(Target::Label(machine_init)),
            ],
        },
    };

    let accept_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "accept".to_string(),
        body: ParsedSentence {
            instructions: vec![
                ParsedInstruction::Jump(Target::Label(machine_accept)),
                ParsedInstruction::Push(ParsedValue::SymbolRef(prefix_sym.clone())),
                ParsedInstruction::SetSingleton,
                ParsedInstruction::Roll(1),
                ParsedInstruction::SetTuple(2),
            ],
        },
    };

    let emit_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "emit".to_string(),
        body: ParsedSentence {
            instructions: vec![
                ParsedInstruction::Jump(Target::Label(machine_emit)),
                ParsedInstruction::Push(ParsedValue::SymbolRef(prefix_sym.clone())),
                ParsedInstruction::SetSingleton,
                ParsedInstruction::Roll(1),
                ParsedInstruction::SetTuple(2),
            ],
        },
    };

    let process_sentence = TopLevelSentence {
        is_exported: false,
        is_test: false,
        name: "process".to_string(),
        body: ParsedSentence {
            instructions: vec![
                ParsedInstruction::Untuple(2),
                ParsedInstruction::Pick(1),
                ParsedInstruction::Push(ParsedValue::SymbolRef(prefix_sym.clone())),
                ParsedInstruction::AssertEqual,
                ParsedInstruction::Drop(1),
                ParsedInstruction::Jump(Target::Label(machine_process)),
            ],
        },
    };

    Ok(vec![
        TopLevelItem::Sentence(init_sentence),
        TopLevelItem::Sentence(accept_sentence),
        TopLevelItem::Sentence(emit_sentence),
        TopLevelItem::Sentence(process_sentence),
    ])
}

fn generate_composition_items(
    composer: &str,
    args: &[Path],
) -> Result<Vec<TopLevelItem>, String> {
    match composer {
        "compose_concurrent" => compose_concurrent(args),
        "compose_hidden" => compose_hidden(args),
        "compose_prefix" => compose_prefix(args),
        _ => Err(format!("Unknown composer: {}", composer)),
    }
}

enum ResolvedItem {
    Symbol(Value),
    Sentence(SentenceIndex),
}

struct Compiler<'a> {
    root_module: &'a Module,
    sentences: Vec<Vec<Instruction>>,
}

impl<'a> Compiler<'a> {
    fn resolve_path(&self, current_path: &[String], path: &Path) -> Result<ResolvedItem, String> {
        let mut curr_node = self.root_module;
        let mut segments_iter = path.segments.iter().peekable();

        if let Some(first) = segments_iter.peek() {
            match first {
                PathSegment::Crate => {
                    segments_iter.next();
                    // curr_node is already root_module
                }
                PathSegment::Super => {
                    let mut up_count = 0;
                    while let Some(PathSegment::Super) = segments_iter.peek() {
                        segments_iter.next();
                        up_count += 1;
                    }
                    if up_count > current_path.len() {
                        return Err(format!("Path goes up too many levels (current path depth: {})", current_path.len()));
                    }
                    let target_depth = current_path.len() - up_count;
                    let target_path = &current_path[..target_depth];
                    for name in target_path {
                        curr_node = curr_node.submodules.get(name)
                            .ok_or_else(|| format!("Internal error: submodule '{}' not found in path navigation", name))?;
                    }
                }
                PathSegment::Identifier(_) => {
                    for name in current_path {
                        curr_node = curr_node.submodules.get(name)
                            .ok_or_else(|| format!("Internal error: submodule '{}' not found in path navigation", name))?;
                    }
                }
            }
        }

        let mut last_name: Option<&str> = None;
        while let Some(seg) = segments_iter.next() {
            match seg {
                PathSegment::Crate => return Err("'crate' can only appear at the beginning of a path".to_string()),
                PathSegment::Super => return Err("'super' can only appear at the beginning of a path".to_string()),
                PathSegment::Identifier(name) => {
                    if segments_iter.peek().is_none() {
                        last_name = Some(name);
                    } else {
                        if let Some(sub) = curr_node.submodules.get(name) {
                            curr_node = sub;
                        } else {
                            return Err(format!("Module '{}' not found in '{}'", name, curr_node.name));
                        }
                    }
                }
            }
        }

        let last_name = last_name.ok_or_else(|| "Empty path after navigation".to_string())?;

        if let Some(val) = curr_node.symbols.get(last_name) {
            Ok(ResolvedItem::Symbol(val.clone()))
        } else if let Some(&idx) = curr_node.sentences.get(last_name) {
            Ok(ResolvedItem::Sentence(idx))
        } else {
            Err(format!("Item '{}' not found in module '{}'", last_name, curr_node.name))
        }
    }

    fn compile_value(&self, current_path: &[String], parsed: ParsedValue) -> Result<Value, String> {
        match parsed {
            ParsedValue::Bool(b) => Ok(Value::Bool(b)),
            ParsedValue::Int(i) => Ok(Value::Int(i)),
            ParsedValue::Float(f) => Ok(Value::Float(f)),
            ParsedValue::Tuple(elements) => {
                let mut compiled_elements = Vec::new();
                for elem in elements {
                    compiled_elements.push(self.compile_value(current_path, elem)?);
                }
                Ok(Value::Tuple(compiled_elements))
            }
            ParsedValue::SymbolRef(path) => {
                match self.resolve_path(current_path, &path)? {
                    ResolvedItem::Symbol(val) => Ok(val),
                    ResolvedItem::Sentence(_) => Err(format!("Expected symbol, found sentence at path {:?}", path)),
                }
            }
            ParsedValue::SetEmpty => Ok(Value::Set(ValueSet::Empty)),
            ParsedValue::SetUniversal => Ok(Value::Set(ValueSet::Universal)),
            ParsedValue::SetSingleton(v) => {
                let val = self.compile_value(current_path, *v)?;
                Ok(Value::Set(ValueSet::Singleton(Box::new(val))))
            }
            ParsedValue::SetUnion(a, b) => {
                let s1 = match self.compile_value(current_path, *a)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in union, found {:?}", other)),
                };
                let s2 = match self.compile_value(current_path, *b)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in union, found {:?}", other)),
                };
                Ok(Value::Set(ValueSet::Union(Box::new(s1), Box::new(s2))))
            }
            ParsedValue::SetIntersection(a, b) => {
                let s1 = match self.compile_value(current_path, *a)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in intersection, found {:?}", other)),
                };
                let s2 = match self.compile_value(current_path, *b)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in intersection, found {:?}", other)),
                };
                Ok(Value::Set(ValueSet::Intersection(Box::new(s1), Box::new(s2))))
            }
            ParsedValue::SetDifference(a, b) => {
                let s1 = match self.compile_value(current_path, *a)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in difference, found {:?}", other)),
                };
                let s2 = match self.compile_value(current_path, *b)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in difference, found {:?}", other)),
                };
                Ok(Value::Set(ValueSet::Intersection(Box::new(s1), Box::new(ValueSet::Complement(Box::new(s2))))))
            }
            ParsedValue::SetComplement(val) => {
                let s = match self.compile_value(current_path, *val)? {
                    Value::Set(s) => s,
                    other => return Err(format!("Expected Set in complement, found {:?}", other)),
                };
                Ok(Value::Set(ValueSet::Complement(Box::new(s))))
            }
            ParsedValue::SetTuple(elements) => {
                let mut compiled_elements = Vec::new();
                for elem in elements {
                    let s = match self.compile_value(current_path, elem)? {
                        Value::Set(s) => s,
                        other => return Err(format!("Expected Set in set_tuple, found {:?}", other)),
                    };
                    compiled_elements.push(s);
                }
                Ok(Value::Set(ValueSet::Tuple(compiled_elements)))
            }
        }
    }

    fn compile_sentence_body(&mut self, current_path: &[String], instructions: Vec<ParsedInstruction>) -> Result<Vec<Instruction>, String> {
        let mut compiled = Vec::new();
        for inst in instructions {
            let c_inst = match inst {
                ParsedInstruction::Push(v) => {
                    let compiled_val = self.compile_value(current_path, v)?;
                    Instruction::Push(compiled_val)
                }
                ParsedInstruction::Drop(d) => Instruction::Drop(d),
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
                ParsedInstruction::Print => Instruction::Print,
                ParsedInstruction::Panic => Instruction::Panic,
                ParsedInstruction::Assert => Instruction::Assert,
                ParsedInstruction::AssertEqual => Instruction::AssertEqual,
                ParsedInstruction::Tuple(n) => Instruction::Tuple(n),
                ParsedInstruction::Untuple(n) => Instruction::Untuple(n),
                ParsedInstruction::And => Instruction::And,
                ParsedInstruction::Or => Instruction::Or,
                ParsedInstruction::SetContains => Instruction::SetContains,
                ParsedInstruction::SetUnion => Instruction::SetUnion,
                ParsedInstruction::SetIntersection => Instruction::SetIntersection,
                ParsedInstruction::SetDifference => Instruction::SetDifference,
                ParsedInstruction::SetComplement => Instruction::SetComplement,
                ParsedInstruction::SetSingleton => Instruction::SetSingleton,
                ParsedInstruction::SetTuple(n) => Instruction::SetTuple(n),
                ParsedInstruction::SetChoose => Instruction::SetChoose,
                ParsedInstruction::SymbolLen => Instruction::SymbolLen,
                ParsedInstruction::SymbolCharAt => Instruction::SymbolCharAt,
                ParsedInstruction::Jump(target) => {
                    let target_idx = self.resolve_target(current_path, target)?;
                    Instruction::Jump(target_idx)
                }
                ParsedInstruction::Branch(t1, t2) => {
                    let idx1 = self.resolve_target(current_path, t1)?;
                    let idx2 = self.resolve_target(current_path, t2)?;
                    Instruction::Branch(idx1, idx2)
                }
            };
            compiled.push(c_inst);
        }
        Ok(compiled)
    }

    fn resolve_target(&mut self, current_path: &[String], target: Target) -> Result<SentenceIndex, String> {
        match target {
            Target::Label(path) => {
                match self.resolve_path(current_path, &path).map_err(|e| format!("Unresolved label target: {}", e))? {
                    ResolvedItem::Sentence(idx) => Ok(idx),
                    ResolvedItem::Symbol(_) => Err(format!("Expected sentence, found symbol at path {:?}", path)),
                }
            }
            Target::Inline(parsed_sentence) => {
                let new_idx = SentenceIndex::from(self.sentences.len());
                self.sentences.push(Vec::new());
                let compiled_body = self.compile_sentence_body(current_path, parsed_sentence.instructions)?;
                let idx_usize: usize = new_idx.into();
                self.sentences[idx_usize] = compiled_body;
                Ok(new_idx)
            }
        }
    }
}

/// Assembles the input text into a `Library` and export/test mappings.
pub fn assemble(input: &str) -> Result<AssemblyResult, String> {
    assemble_with_path(input, None)
}

/// Assembles the input text with an optional base directory context for resolving external modules.
pub fn assemble_with_path(input: &str, base_dir: Option<&std::path::Path>) -> Result<AssemblyResult, String> {
    let tokens = tokenize(input)?;
    let mut stream = TokenStream { tokens, position: 0 };
    let items = parse_top_level(&mut stream, base_dir)?;

    let mut root_module = Module::new("crate".to_string());
    let mut symbol_counter = 0;
    let mut sentence_counter = 0;
    let mut flat_sentences = Vec::new();
    let mut exports = HashMap::new();
    let mut tests = HashMap::new();

    let mut current_path = Vec::new();
    build_module_tree(
        items,
        &mut current_path,
        &mut symbol_counter,
        &mut sentence_counter,
        &mut root_module,
        &mut flat_sentences,
        &mut exports,
        &mut tests,
    )?;

    let mut compiler = Compiler {
        root_module: &root_module,
        sentences: Vec::new(),
    };

    // Pre-allocate space for all named sentences
    compiler.sentences.resize(sentence_counter, Vec::new());

    // Compile instructions recursively
    for (idx, (path, sentence)) in flat_sentences.into_iter().enumerate() {
        let compiled_instructions = compiler.compile_sentence_body(&path, sentence.body.instructions)?;
        compiler.sentences[idx] = compiled_instructions;
    }

    let mut library = Library::new();
    for s in compiler.sentences {
        library.sentences.push(s);
    }

    Ok(AssemblyResult {
        library,
        exports,
        tests,
    })
}
