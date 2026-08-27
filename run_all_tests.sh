#!/usr/bin/env bash

# Top-level shell script to run both Rust unit/VM tests and Hanoi (.hana) integration tests

set -euo pipefail

# Ensure we are in the script's directory; the workspace is `lang/` under it.
CDPATH="" cd -- "$(dirname -- "$0")"

echo "======================================"
echo "Running cargo test..."
echo "======================================"
echo ""

if ! (cd lang && cargo test); then
    echo "======================================"
    echo "FAILED: cargo test failed."
    exit 1
fi

echo ""
echo "======================================"
echo "Running Hanoi integration tests..."
echo "======================================"
echo ""
if ! ./run_tests.sh "$@"; then
    echo "======================================"
    echo "FAILED: Hanoi integration tests failed."
    exit 1
fi

echo ""
echo "======================================"
echo "All tests passed successfully!"
echo "======================================"
