#!/usr/bin/env bash
# Build one declared live Lean umbrella from source under the pinned project toolchain.
#
# This is an exterior formal receiver, never an inference phase. It deliberately has no archived
# `.olean` fallback and does not reinterpret missing aggregator imports as success.
#
#   bash tools/lean_check.sh
#   bash tools/lean_check.sh ElementaryHolonics.Computation.HolonicMachineLearning

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT="$ROOT/soma/formal/elementary-holonics"
TARGET="${1:-ElementaryHolonics.Computation.HolonicMachineLearning}"

if [ ! -f "$PROJECT/lakefile.toml" ] || [ ! -f "$PROJECT/lean-toolchain" ]; then
    printf 'formal project is incomplete: %s\n' "$PROJECT" >&2
    exit 2
fi

cd "$PROJECT"
LEAN_LOG="$(mktemp)"
trap 'rm -- "$LEAN_LOG"' EXIT
if ! timeout -k 2s 180s lake build "$TARGET" 2>&1 | tee "$LEAN_LOG"; then
    exit 1
fi
if grep -Fq "declaration uses 'sorry'" "$LEAN_LOG"; then
    printf "formal target contains a declaration elaborated with sorry/admit: %s\n" "$TARGET" >&2
    exit 1
fi
