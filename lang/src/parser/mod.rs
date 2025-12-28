use std::{collections::VecDeque, path::PathBuf, result};

use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;

use source::{Loader, Sources};

use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::parser::source::FileIndex;

pub mod source;

#[derive(Parser)]
#[grammar = "parser/hanoi.pest"]

struct HanoiParser;

pub fn load_all(loader: &Loader) -> anyhow::Result<(Sources, Library)> {
    let mut sources = Sources::default();
    let mut queue = VecDeque::from([PathBuf::from("")]);
    let mut library = Library::default();
    while let Some(mod_name) = queue.pop_front() {
        let file_idx = loader.load(mod_name.clone(), &mut sources)?;
        let factory = Factory(file_idx);

        let parsed = HanoiParser::parse(Rule::file, &sources.files[file_idx].source)?
            .next()
            .unwrap();
        let file = factory.file(parsed);

        for import in file.imports.iter() {
            queue.push_back(mod_name.join(import.0.as_str(&sources)));
        }

        library.files.push(file);
    }

    Ok((sources, library))
}

#[derive(Debug, Default)]
pub struct Library {
    pub files: TiVec<FileIndex, File>,
}

struct Factory(FileIndex);

impl Factory {
    fn file(&self, p: Pair<Rule>) -> File {
        assert_eq!(p.as_rule(), Rule::file_body);
        let pairs = p.into_inner();
        let mut result = File::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::external_mod_decl => result
                    .imports
                    .push(self.identifier(pair.into_inner().exactly_one().unwrap())),
                Rule::decl => result.namespace.decls.push(self.decl(pair)),
                _ => panic!("invalid file item: {:?}", pair.as_rule()),
            }
        }
        result
    }

    fn decl(&self, p: Pair<Rule>) -> Decl {
        assert_eq!(p.as_rule(), Rule::decl);
        let inner = p.into_inner().exactly_one().unwrap();
        match inner.as_rule() {
            Rule::const_decl => Decl::ConstDecl(self.const_decl(inner)),
            _ => panic!("invalid decl: {:?}", inner.as_rule()),
        }
    }

    fn const_decl(&self, p: Pair<Rule>) -> ConstDecl {
        assert_eq!(p.as_rule(), Rule::const_decl);
        let (name, expr) = p.into_inner().collect_tuple().unwrap();
        ConstDecl {
            name: self.identifier(name),
            value: self.const_expr(expr),
        }
    }

    fn identifier(&self, p: Pair<Rule>) -> Identifier {
        assert_eq!(p.as_rule(), Rule::identifier);
        let span = source::Span::from_ast(self.0, p.as_span());
        Identifier(span)
    }

    fn const_expr(&self, p: Pair<Rule>) -> ConstExpr {
        assert_eq!(p.as_rule(), Rule::const_expr);
        let inner = p.into_inner().exactly_one().unwrap();

        match inner.as_rule() {
            Rule::literal => ConstExpr::Literal(self.literal(inner)),
            Rule::path => ConstExpr::Path(self.path(inner)),
            _ => panic!("invalid const expr"),
        }
    }

    fn literal(&self, p: Pair<Rule>) -> Literal {
        assert_eq!(p.as_rule(), Rule::literal);
        let inner = p.into_inner().exactly_one().unwrap();
        let span = source::Span::from_ast(self.0, inner.as_span());
        let ty = match inner.as_rule() {
            Rule::int => LiteralType::Int,
            Rule::char_lit => LiteralType::Char,
            Rule::bool => LiteralType::Bool,
            Rule::symbol => LiteralType::Symbol,
            _ => panic!("invalid literal type"),
        };
        Literal { ty, span }
    }

    fn path(&self, p: Pair<Rule>) -> Path {
        assert_eq!(p.as_rule(), Rule::path);
        let span = source::Span::from_ast(self.0, p.as_span());
        let segments = p.into_inner().map(|p| self.identifier(p)).collect();
        Path { span, segments }
    }
}

#[derive(Debug, Default)]
pub struct File {
    pub imports: Vec<Identifier>,
    pub namespace: Namespace,
}

#[derive(Debug, Default)]
pub struct Namespace {
    // pub uses: Vec<Use>,
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub enum Decl {
    ConstDecl(ConstDecl),
    // SentenceDecl(SentenceDecl),
    // FnDecl(FnDecl),
    // DefDecl(DefDecl),
}

#[derive(Debug)]
pub struct ConstDecl {
    pub name: Identifier,
    pub value: ConstExpr,
}

#[derive(Debug)]
pub enum ConstExpr {
    Literal(Literal),
    Path(Path),
}

#[derive(Debug)]
pub struct Literal {
    pub ty: LiteralType,
    pub span: source::Span,
}

#[derive(Debug)]
pub enum LiteralType {
    Int,
    Char,
    Bool,
    Symbol,
}

#[derive(Debug)]
pub struct Path {
    span: source::Span,
    segments: Vec<Identifier>,
}

#[derive(Debug)]
pub struct Identifier(source::Span);
