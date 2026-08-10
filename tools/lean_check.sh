#!/usr/bin/env bash
# Give the formal sources a verdict.
#
# `soma/formal` carries the only mathematics in this tree that a kernel can grade, and until
# 2026-08-09 it received **no verdict at all** — not because it was wrong, but because mathlib was
# never on the search path. The oleans were already built and sitting in `archive/cpp-engine/formal`:
# 2,623 for mathlib alone, toolchain v4.27.0, and the live sources are byte-identical to the archived
# ones. This is a path variable, not a build.
#
# The layout detail that costs an hour if you miss it: Lean 4.27 puts oleans under
# `.lake/build/lib/lean/`, not `.lake/build/lib/`. A path without the trailing `lean` fails with
# "unknown module prefix 'Mathlib'" while the directory plainly exists.
#
# THIS IS NOT A GATE AND NOT AN ORGAN. The kernel is an external receiver whose verdict is a
# RETURN, graded in batch on an already-constructed population. `CLAUDE.md` §13 rule 2: a foreign
# process deciding what the body may construct is `G_authored`. Nothing here belongs in a
# construction loop.
#
#     bash tools/lean_check.sh            # check every project, report clean/issue per file
#     bash tools/lean_check.sh --control  # prove the check can fail, then check
#
# Exits non-zero if any file that previously checked clean now does not.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKE="$ROOT/archive/cpp-engine/formal/elementary-holonics/.lake"

if [ ! -d "$LAKE/packages/mathlib/.lake/build/lib/lean" ]; then
  echo "the built mathlib is not where this script expects it:"
  echo "  $LAKE/packages/mathlib/.lake/build/lib/lean"
  echo "nothing here builds mathlib; if the archive moved, this path moves with it."
  exit 2
fi

LEAN_PATH="$LAKE/build/lib/lean"
for p in "$LAKE"/packages/*/; do
  [ -d "$p.lake/build/lib/lean" ] && LEAN_PATH="$LEAN_PATH:$p.lake/build/lib/lean"
done
export LEAN_PATH

if [ "${1:-}" = "--control" ]; then
  # A check that cannot fail carries no evidence. Prove this one can, before trusting it.
  ctl="$(mktemp -d)"
  cp -r "$ROOT/soma/formal/elementary-holonics/." "$ctl/"
  printf '\ntheorem deliberately_false : (1 : Nat) = 2 := rfl\n' \
    >> "$ctl/ElementaryHolonics/RH/Statement.lean"
  echo "CONTROL — a deliberately false theorem appended to RH/Statement.lean:"
  ( cd "$ctl" && lean --root=. ElementaryHolonics/RH/Statement.lean 2>&1 | sed 's/^/    /' | head -5 )
  rm -rf "$ctl"
  echo
fi

clean=0; issue=0
for project in "$ROOT"/soma/formal/*/; do
  name="$(basename "$project")"
  echo "=== $name"
  while IFS= read -r file; do
    out="$(cd "$project" && lean --root=. "$file" 2>&1)"; rc=$?
    if [ $rc -eq 0 ] && [ -z "$out" ]; then
      printf '  CLEAN  %s\n' "$file"; clean=$((clean + 1))
    elif printf '%s' "$out" | grep -q "unknown module prefix '$(basename "$file" .lean)'"; then
      # A root aggregator imports its own leaves, whose oleans a source check does not produce.
      # Build order, not a source defect — reported so it is legible, not counted as an issue.
      printf '  ROOT   %s (aggregator; needs its own leaves built)\n' "$file"
    else
      printf '  ISSUE  %s\n' "$file"
      printf '%s' "$out" | sed 's/^/         /' | head -4
      issue=$((issue + 1))
    fi
  done < <(cd "$project" && find . -name '*.lean' | sort)
done

echo
echo "clean=$clean  issue=$issue"
[ "$issue" -eq 0 ]
