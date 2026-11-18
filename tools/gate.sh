#!/usr/bin/env bash
# Gate 1 for any code change (CLAUDE.md): the workspace check, the guard lints of THE_ENGINE §9
# (no floats, no disallowed types or methods: guards 7 and 12) on the engine and on athena, and the engine's
# doctests. A guard that is not run does not hold: the lint receipt had failed unnoticed since October 1
# because gate 1 was `cargo check` alone. The October library's constructions (guards 2, 3, 10, 16, 18, 20
# to 22 and their compile_fail doctests) retired with it in C8c of #603; THE_MACHINE's table gives each
# guard's end. Run from the repository root; CARGO_TARGET_DIR should be the worktree's own.
set -u -o pipefail
status=0
run() { local name=$1; shift; local start; start=$(date +%s%3N)
  if "$@"; then printf 'gate %s: ok (%s ms)\n' "$name" "$(( $(date +%s%3N) - start ))"
  else printf 'gate %s: FAILED (%s ms)\n' "$name" "$(( $(date +%s%3N) - start ))"; status=1; fi; }
run check cargo check --workspace --all-targets
# The engine's host tests (`hnn::tower::field` and its moment's and scale's; C2 of the consolidation, #603). Gate 1 had run none of them
# until November 14. One takes about 150 s in debug against 49 s for the other 122 together (measured November 14), so it runs in gate 2,
# with the tests of a step that changes the engine: `cargo test -p holonics-engine --lib the_covector_matches_the_code_across_the_far_support`.
# Since C3 the engine is its own crate (`crates/engine`), and the guard lints and doctests run on it too.
run engine-host-tests cargo test -p holonics-engine --lib field -- --skip the_covector_matches_the_code_across_the_far_support
# `--no-deps` lints exactly the named crates: since C6 the harness's dev-dependency on athena reaches the card crate, whose
# yardsticks still owe their float lints, and clippy lints a workspace member it compiles as a dependency.
run guard-lints cargo clippy -p holonics-engine --all-targets --no-deps -- -D clippy::disallowed_types \
  -D clippy::disallowed_methods -D clippy::float_arithmetic
run guard-doctests env RUSTC_BOOTSTRAP=1 cargo test -p holonics-engine --doc
# The commands (`crates/athena`, C6 of #603): the exterior, so files and processes are lawful there by the crate's own allow,
# and the float guard runs (a reading's printed floats are allowed where they are written). `--no-deps`, because the card
# crate's yardsticks still owe their float lints (THE_CONSOLIDATION, C3).
run athena-guard-lints cargo clippy -p athena --all-targets --no-deps -- -D clippy::disallowed_types -D clippy::disallowed_methods \
  -D clippy::float_arithmetic
run athena-tests cargo test -p athena
run trunk-census-controls python3 tools/test_repo_census.py
run travel-rank-controls python3 tools/test_state_travel.py
run block-direction-controls python3 tools/test_block_directions.py
run part-rate-controls python3 tools/test_part_rates.py
run founding-strength-controls python3 tools/test_founding_strength.py
run residual-block-controls python3 tools/test_residual_blocks.py
run run-watch-controls python3 tools/test_runs.py
run lap-check-controls python3 tools/test_lap_check.py
run reproduction-controls python3 tools/test_reproduction.py
run live-set-controls python3 tools/test_live_set.py
run measure-controls python3 tools/test_measure.py
run loudness-table-controls python3 tools/test_loudness_table.py
run tension-ruler-controls python3 tools/test_tension_ruler.py
run mailbox-controls python3 tools/test_agent_mailbox.py
run copy-length-controls python3 tools/test_copy_length.py
run human-messages-controls python3 tools/test_human_messages.py
run link-check-controls python3 tools/test_link_check.py
# The text against the tree (C9 of #603): every relative link of the root guides, docs/ and the records' README resolves, and
# every atlas owner that names the tree stands in it. A link test that nothing runs does not hold.
run guide-links python3 tools/link_check.py links
run atlas-owners python3 tools/link_check.py atlas
# The records' index is what the file names give today; where it is behind: python3 tools/records_index.py write
run records-index-controls python3 tools/test_records_index.py
exit $status
