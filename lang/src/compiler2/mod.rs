

use crate::{
    bytecode,
    parser::{self, source},
};

pub mod ast;
pub mod linked;
pub mod unlinked;

pub fn compile(loader: &source::Loader) -> anyhow::Result<bytecode::Library> {
    let (sources, parsed_library) = parser::load_all(&loader)?;

    let unlinked = unlinked::Library::from_parsed(&sources, parsed_library);

    let linked = unlinked.link(&sources)?;

    let bytecode = linked.into_bytecode(&sources);

    Ok(bytecode)
}
