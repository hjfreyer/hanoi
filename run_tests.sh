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

failed=0
passed=0

for test_file in tests/*.hana; do
    echo "--------------------------------------"
    echo "Running tests in: $test_file"
    echo "--------------------------------------"
    
    if ./target/debug/test-runner "$test_file"; then
        passed=$((passed + 1))
    else
        failed=$((failed + 1))
    fi
    echo ""
done

echo "======================================"
if [ "$failed" -eq 0 ]; then
    echo "All integration test files passed ($passed files)."
    exit 0
else
    echo "FAILED: $failed test files failed ($passed passed)."
    exit 1
fi
