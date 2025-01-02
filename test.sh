set -e

cargo run -- test data/ list
cargo run -- test data/ iter
cargo run -- test data/ main