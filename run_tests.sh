#!/usr/bin/env bash

# Top-level shell script to run all Hanoi (.hana) test files

set -euo pipefail

# Ensure we are in the script's directory
CDPATH="" cd -- "$(dirname -- "$0")"

echo "Building test runner..."
cargo build --bin test-runner

echo ""
echo "======================================"
echo "Running Hanoi integration tests..."
echo "======================================"
echo ""

if ./target/debug/test-runner tests "$@"; then
    echo "======================================"
    echo "All integration tests passed."
    exit 0
else
    echo "======================================"
    echo "FAILED: Integration tests failed."
    exit 1
fi
