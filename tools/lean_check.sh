#!/usr/bin/env bash
# Build declared live Lean targets from source under the pinned project toolchain.
#
# This is an exterior formal receiver, never an inference phase. It deliberately has no archived
# `.olean` fallback and does not reinterpret missing aggregator imports as success.
#
#   bash tools/lean_check.sh
#   bash tools/lean_check.sh ElementaryHolonics.Framework.Geometry
#   bash tools/lean_check.sh ElementaryHolonics

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT="$ROOT/formal/elementary-holonics"
if [ "$#" -eq 0 ]; then
    set -- ElementaryHolonics.Framework
fi

if [ ! -f "$PROJECT/lakefile.toml" ] || [ ! -f "$PROJECT/lean-toolchain" ]; then
    printf 'formal project is incomplete: %s\n' "$PROJECT" >&2
    exit 2
fi

cd "$PROJECT"
LEAN_LOG="$(mktemp)"
trap 'rm -- "$LEAN_LOG"' EXIT
if ! lake build "$@" 2>&1 | tee "$LEAN_LOG"; then
    exit 1
fi
if grep -Fq "declaration uses 'sorry'" "$LEAN_LOG"; then
    printf "formal target contains a declaration elaborated with sorry/admit: %s\n" "$*" >&2
    exit 1
fi
