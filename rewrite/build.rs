//! Nothing to build. See the `syn` build dependency in `Cargo.toml`.
fn main() {
    println!("cargo::rerun-if-changed=build.rs");
}
