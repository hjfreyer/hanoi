set -e
cargo build --release

BIN=target/release/hanoi
$BIN test data/ builtin
$BIN test data/ list
$BIN test data/ iter
$BIN test data/ ssv
$BIN test data/ str
$BIN test data/ main
$BIN test data/ multi_iter
$BIN test data/ adv1p1