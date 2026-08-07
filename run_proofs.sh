#!/usr/bin/env bash

# Top-level shell script to check every `identity` stated in tests/ against the
# proof in the `.hant` beside the `.hana` that states it.
#
# Separate from run_tests.sh rather than a line in it: that script forwards
# "$@" to test-runner, whose flags (--test-filter, --test-gas) mean nothing
# here. `prove` has its own.

set -euo pipefail

# Ensure we are in the script's directory
CDPATH="" cd -- "$(dirname -- "$0")"

echo "Building prove..."
cargo build --bin prove

echo ""
echo "======================================"
echo "Checking Hanoi identities..."
echo "======================================"
echo ""

if ./target/debug/prove tests "$@"; then
    echo "======================================"
    echo "All identities proved."
    exit 0
else
    echo "======================================"
    echo "FAILED: an identity is unproved."
    exit 1
fi
