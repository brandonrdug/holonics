#!/usr/bin/env bash
# Gate 1 for any code change (CLAUDE.md, AGENTS.md): the workspace check, THE_MACHINE's guard lints
# (no floats, no disallowed types or methods: guards 7 and 12) and the guards' compile_fail
# doctests (guards 2, 3, 4, 10, 16, 18 and the rest that are type constructions). A guard that is
# not run does not hold: the lint receipt had failed unnoticed since October 1 because gate 1 was
# `cargo check` alone. Run from the repository root; CARGO_TARGET_DIR should be the worktree's own.
set -u -o pipefail
status=0
run() { local name=$1; shift; local start; start=$(date +%s%3N)
  if "$@"; then printf 'gate %s: ok (%s ms)\n' "$name" "$(( $(date +%s%3N) - start ))"
  else printf 'gate %s: FAILED (%s ms)\n' "$name" "$(( $(date +%s%3N) - start ))"; status=1; fi; }
run check cargo check --workspace --all-targets
run guard-lints cargo clippy -p holonics --all-targets -- -D clippy::disallowed_types \
  -D clippy::disallowed_methods -D clippy::float_arithmetic
run guard-doctests env RUSTC_BOOTSTRAP=1 cargo test -p holonics --doc hnn
exit $status
