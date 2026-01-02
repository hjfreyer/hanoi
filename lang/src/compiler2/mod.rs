use crate::{
    bytecode,
    parser::{self, source},
};
use debug_with_trait::DebugWith;
pub mod ast;
pub mod linked;
pub mod unlinked;
pub mod unresolved;

pub fn compile(loader: &source::Loader) -> anyhow::Result<bytecode::Library> {
    let (sources, parsed_library) = parser::load_all(&loader)?;

    let unresolved = unresolved::Library::from_parsed(&sources, parsed_library);
    dbg!(unresolved.convert(&sources));
    let unlinked = unresolved.resolve(&sources)?;

    let linked = unlinked.link(&sources)?;

    let bytecode = linked.into_bytecode(&sources);

    Ok(bytecode)
}
