set -e
cargo build --release

BIN=target/release/hanoi
$BIN test data/ list
$BIN test data/ iter
$BIN test data/ ssv
$BIN test data/ str
$BIN test data/ main