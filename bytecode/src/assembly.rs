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
        "set_singleton" => Ok(ParsedInstruction::SetSingleton),
        "set_tuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::SetTuple(size))
        }
        "set_choose" => Ok(ParsedInstruction::SetChoose),
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
}

struct TopLevelSentence {
    is_exported: bool,
    is_test: bool,
    name: String,
    body: ParsedSentence,
}

fn parse_top_level(stream: &mut TokenStream) -> Result<Vec<TopLevelItem>, String> {
    parse_items(stream, None)
}

fn parse_items(stream: &mut TokenStream, end_token: Option<Token>) -> Result<Vec<TopLevelItem>, String> {
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
            stream.expect(Token::LBrace)?;
            let mod_items = parse_items(stream, Some(Token::RBrace))?;
            stream.expect(Token::RBrace)?;
            items.push(TopLevelItem::Mod { name, items: mod_items });
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
    SetSingleton,
    SetTuple(usize),
    SetChoose,
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
        }
    }
    Ok(())
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
                Ok(Value::Set(ValueSet::Difference(Box::new(s1), Box::new(s2))))
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
                ParsedInstruction::SetSingleton => Instruction::SetSingleton,
                ParsedInstruction::SetTuple(n) => Instruction::SetTuple(n),
                ParsedInstruction::SetChoose => Instruction::SetChoose,
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
    let tokens = tokenize(input)?;
    let mut stream = TokenStream { tokens, position: 0 };
    let items = parse_top_level(&mut stream)?;

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
