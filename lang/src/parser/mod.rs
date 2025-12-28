use std::{collections::VecDeque, path::PathBuf};

use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;

use source::{Loader, Sources};

use itertools::Itertools;

use crate::parser::source::FileIndex;

pub mod source;

#[derive(Parser)]
#[grammar = "hanoi.pest"]

struct HanoiParser;

pub fn load_all(loader: &Loader) -> anyhow::Result<Sources> {
    let mut sources = Sources::default();
    let mut queue = VecDeque::from([PathBuf::from("")]);

    while let Some(mod_name) = queue.pop_front() {
        let file_idx = loader.load(mod_name.clone(), &mut sources)?;
        let factory = Factory(file_idx);

        let parsed = HanoiParser::parse(Rule::file, &sources.files[file_idx].source)?;
        let file = factory.file(parsed);

        for import in file.imports {
            queue.push_back(mod_name.join(import.name));
        }
    }

    Ok(sources)
}

struct Factory(FileIndex);

impl Factory {
    fn file(&self, pairs: Pairs<Rule>) -> File {
        let imports = pairs
            .filter_map(|p| {
                if p.as_rule() == Rule::ns_import {
                    Some(self.identifier(p.into_inner().exactly_one().unwrap()))
                } else {
                    None
                }
            })
            .collect();
        File { imports }
    }

    fn identifier(&self, p: Pair<Rule>) -> Identifier {
        assert_eq!(p.as_rule(), Rule::identifier);
        let span = source::Span::from_ast(self.0, p.as_span());
        Identifier {
            name: p.as_str().to_string(),
            span,
        }
    }
}

#[derive(Debug)]
struct File {
    pub imports: Vec<Identifier>,
}

#[derive(Debug)]
struct Identifier {
    pub name: String,
    pub span: source::Span,
}
