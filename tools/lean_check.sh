#!/usr/bin/env bash
# Build one declared live Lean umbrella from source under the pinned project toolchain.
#
# This is an exterior formal receiver, never an inference phase. It deliberately has no archived
# `.olean` fallback and does not reinterpret missing aggregator imports as success.
#
#   bash tools/lean_check.sh
#   bash tools/lean_check.sh ElementaryHolonics.Computation.HolonicQuantumTransport

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT="$ROOT/formal/elementary-holonics"
TARGET="${1:-ElementaryHolonics.Computation.HolonicQuantumTransport}"

if [ ! -f "$PROJECT/lakefile.toml" ] || [ ! -f "$PROJECT/lean-toolchain" ]; then
    printf 'formal project is incomplete: %s\n' "$PROJECT" >&2
    exit 2
fi

cd "$PROJECT"
LEAN_LOG="$(mktemp)"
trap 'rm -- "$LEAN_LOG"' EXIT
if ! lake build "$TARGET" 2>&1 | tee "$LEAN_LOG"; then
    exit 1
fi
if grep -Fq "declaration uses 'sorry'" "$LEAN_LOG"; then
    printf "formal target contains a declaration elaborated with sorry/admit: %s\n" "$TARGET" >&2
    exit 1
fi
