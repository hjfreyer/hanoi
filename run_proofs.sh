#!/usr/bin/env bash

# Top-level shell script to check every `identity` stated in tests/ against the
# proof in the `.hant` beside the `.hana` that states it — and then to check the
# derivations that produced against the corpus a second time, through the file
# format, with the search taken away.
#
# Separate from run_tests.sh rather than a line in it: that script forwards
# "$@" to test-runner, whose flags (--test-filter, --test-gas) mean nothing
# here. `prove` has its own.

set -euo pipefail

# Ensure we are in the script's directory
CDPATH="" cd -- "$(dirname -- "$0")"

echo "Building prove and replay..."
cargo build --bin prove --bin replay

DERIVATIONS="$(mktemp -t hanoi-derivations.XXXXXX.hand)"
trap 'rm -f "$DERIVATIONS"' EXIT

echo ""
echo "======================================"
echo "Checking Hanoi identities..."
echo "======================================"
echo ""

if ! ./target/debug/prove tests --emit "$DERIVATIONS" "$@"; then
    echo "======================================"
    echo "FAILED: an identity is unproved."
    exit 1
fi

# The same claims, decided a second way. `prove` compiles a tactic and searches;
# this reads the derivation that search wrote down and replays it, so what is
# being checked here is the format and the applier alone — the path any producer
# in any language takes. `--complete` is what makes it a gate rather than a
# sample: every identity the corpus states has to be in the file.
echo ""
echo "======================================"
echo "Replaying the derivations..."
echo "======================================"
echo ""

if ! ./target/debug/replay tests "$DERIVATIONS" --complete; then
    echo "======================================"
    echo "FAILED: a derivation does not replay."
    exit 1
fi

echo "======================================"
echo "All identities proved, and every derivation replays."
exit 0
