#!/usr/bin/env bash

# Top-level shell script to run all Hanoi (.hana) test files

set -euo pipefail

# The workspace is `lang/`; the corpus it runs is `hana/`, beside it.
CDPATH="" cd -- "$(dirname -- "$0")"

echo "Building test runner..."
(cd lang && cargo build --bin test-runner)

echo ""
echo "======================================"
echo "Running Hanoi integration tests..."
echo "======================================"
echo ""

if ./lang/target/debug/test-runner hana "$@"; then
    echo "======================================"
    echo "All integration tests passed."
    exit 0
else
    echo "======================================"
    echo "FAILED: Integration tests failed."
    exit 1
fi
