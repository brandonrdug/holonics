#!/usr/bin/env bash
# Gate 1 for any code change (CLAUDE.md, AGENTS.md): the workspace check, THE_MACHINE's guard lints
# (no floats, no disallowed types or methods: guards 7 and 12) and the guards' doctests: every
# library doctest, so the compile_fail constructions in `hnn` (guards 2, 3, 4, 10, 16, 18), on the
# receiver's sealed families (guard 20, `receiver::population`), at the wave chain's producing
# receiver, and at the notebook's exterior (guards 19, 21, 22, `exterior_guards`) all run. A guard
# that is not run does not hold: the lint receipt had failed unnoticed since October 1 because gate
# 1 was `cargo check` alone, and until October 5 the doctests outside `hnn` were filtered out. Run
# from the repository root; CARGO_TARGET_DIR should be the worktree's own.
set -u -o pipefail
status=0
run() { local name=$1; shift; local start; start=$(date +%s%3N)
  if "$@"; then printf 'gate %s: ok (%s ms)\n' "$name" "$(( $(date +%s%3N) - start ))"
  else printf 'gate %s: FAILED (%s ms)\n' "$name" "$(( $(date +%s%3N) - start ))"; status=1; fi; }
run check cargo check --workspace --all-targets
# The engine's host tests (`hnn::tower::field` and its moment's and scale's; C2 of the consolidation, #603). Gate 1 had run none of them
# until November 14. One takes about 150 s in debug against 49 s for the other 122 together (measured November 14), so it runs in gate 2,
# with the tests of a step that changes the engine: `cargo test -p holonics --lib the_covector_matches_the_code_across_the_far_support`.
run engine-host-tests cargo test -p holonics --lib hnn::tower::field -- --skip the_covector_matches_the_code_across_the_far_support
run guard-lints cargo clippy -p holonics --all-targets -- -D clippy::disallowed_types \
  -D clippy::disallowed_methods -D clippy::float_arithmetic
run guard-doctests env RUSTC_BOOTSTRAP=1 cargo test -p holonics --doc
run diagnostic-timing-controls cargo test -p holonics --example listener continuing::diagnostic::
run diagnostic-supervisor-controls python3 tools/test_listener_diagnostic_stage.py
run diagnostic-receipt-controls python3 tools/test_listener_diagnostic_receipts.py
run trunk-census-controls python3 tools/test_repo_census.py
run travel-rank-controls python3 tools/test_state_travel.py
run block-direction-controls python3 tools/test_block_directions.py
run part-rate-controls python3 tools/test_part_rates.py
run founding-strength-controls python3 tools/test_founding_strength.py
run residual-block-controls python3 tools/test_residual_blocks.py
run seen-passage-controls python3 tools/test_seen_passage.py
run run-watch-controls python3 tools/test_runs.py
run reproduction-controls python3 tools/test_reproduction.py
run live-set-controls python3 tools/test_live_set.py
run measure-controls python3 tools/test_measure.py
run listener-continuation-controls cargo test -p holonics --example listener continuing::tests::
run projected-statistics-controls cargo test -p holonics --lib projected_statistics_tests
run native-class-advance-controls cargo test -p holonics --lib class_advance_tests
run native-gram-carry-conservation cargo test -p holonics --lib gram_carry_conservation_tests
run finite-solenoidal-controls cargo test -p holonics --lib solenoid
run rational-place-controls cargo test -p holonics --lib ratio::places::tests::
run plural-coupling-controls cargo test -p holonics --lib receiver::coupling::tests::
run grouped-tube-controls cargo test -p holonics --lib constitution::tube_tests
run observed-tube-controls cargo test -p holonics --lib observed_tube_passage
run source-refinement-controls cargo test -p holonics --lib source_refinement_tests
run actual-source-alignment cargo test -p holonics --lib actual_source_face_reads
run actual-ray-joint-controls cargo test -p holonics --lib actual_ray_
run actual-factor-refusal cargo test -p holonics --lib nonlinear_material_and_finer_source
run refined-source-native-restore cargo test -p holonics --lib refined_source_map_is_consumed
run solenoidal-listener-controls cargo test -p holonics --example listener solenoidal
run offline-coupling-controls cargo test -p holonics --example solenoidal_coupling
exit $status
