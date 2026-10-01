#!/usr/bin/env bash
# Loop 1c's declared runs (THE_REBUILD U6, step 1, loop 1c; the pin
# research/records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md).
#
# Every run uses this worktree's release build of `hnn_prediction`, at most 19 rayon threads (the
# pin §6: the host's 24 less Codex's reserved 5), its artifacts in the worktree's `.local/1c/`, and an
# outer `timeout` fixed from the measured cost reads (the pin §6), never raised. Each run is launched
# in the background; its receipt carries its projection, deadline, wall time and peak resident set
# (bash's `time` and the harness's resident line).
#
#   bash research/notebook/hnn_design/loop_1c_runs.sh <run>
#
# The cost reads (development reads only, the pin §6.1): `cost-replay` (gate A's saved state
# restored and read), `cost-move` (gate A's first native move replayed, its states written),
# `cost-coupling` (one constitution's persistence and coupling reads, on the timing seed's founded
# opening), `cost-represent` (one iterate of the exterior fit, on the timing seed).
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
out=.local/1c
mkdir -p "$out"
bin=target/release/examples/hnn_prediction
export RAYON_NUM_THREADS=19
gate_a=research/records/2026-09-30_STEP_1B_GATE_A_receipts

run() {
  # run <name> <guard seconds> <args…>: stdout to <name>.txt, stderr to <name>.err, the wall and
  # CPU times and the exit to <name>.time (the peak resident set is the harness's own last line).
  local name=$1 guard=$2
  shift 2
  local TIMEFORMAT="wall %R s, user %U s, system %S s, cpu %P percent"
  local status=0
  { time timeout "$guard" "$bin" "$@" > "$out/$name.txt" 2> "$out/$name.err"; } 2> "$out/$name.time" || status=$?
  echo "exit $status (124: the outer guard of $guard s)" >> "$out/$name.time"
}

cargo build --release -q -j 12 -p holonics --example hnn_prediction

case "${1:-}" in
  cost-replay)
    run cost_replay 600 executed replay order2 2026093061 8 \
      "constitution 1 (before move 1)=$gate_a/witness_best.state"
    ;;
  check-cost-replay)
    # The restored state's reading against gate A's receipt: its summary line (the wall time
    # masked) and its 64 decision terms whole (with the 8 requests' release lines).
    mask='s/; [0-9]+ ms$//'
    diff <(sed -n '4p' "$gate_a/witness.txt" | sed -E "$mask") \
      <(sed -n '2p' "$out/cost_replay.txt" | sed -E "$mask")
    diff <(sed -n '36,107p' "$gate_a/witness.txt") <(sed -n '3,74p' "$out/cost_replay.txt")
    grep -q "identical to its file" "$out/cost_replay.err"
    echo "the restored state's reading matches gate A's receipt (1 summary line, 72 term lines), and the state writes back to its file"
    ;;
  cost-move)
    mkdir -p "$out/cost_move_states"
    run cost_move 900 executed witness order2 2026093061 8 1 494208 \
      "$out/cost_move_best.state" "$out/cost_move_states"
    ;;
  check-cost-move)
    # Gate A's first native move replayed: its constitution and move lines (wall times masked),
    # constitution 1's reading (its label masked), and the written state against the saved one.
    mask='s/; [0-9]+ ms$//; s/constitution 1 \((before move 1|after the last move)\)/constitution 1/'
    diff <(sed -n '2,4p' "$gate_a/witness.txt" | sed -E "$mask") \
      <(sed -n '2,4p' "$out/cost_move.txt" | sed -E "$mask")
    cmp "$out/cost_move_states/c1.state" "$gate_a/witness_best.state"
    echo "gate A's first move replays exactly: 3 lines, and constitution 1's complete continuing state is byte-identical to gate A's saved state"
    ;;
  cost-coupling)
    run cost_coupling 1800 executed coupling order2 2026093062 8 1200000 opening=opening
    ;;
  cost-represent)
    run cost_represent 1800 executed represent order2 2026093062 8 1 1200000 \
      "$out/cost_represent_best.txt"
    ;;
  cost-coupling-12)
    # Phase 2's schedule (the pin §6.3): one constitution's coupling reads at 12 threads, read
    # while the exterior fit holds its 7.
    RAYON_NUM_THREADS=12 run cost_coupling_12 1800 executed coupling order2 2026093062 8 1200000 opening=opening
    ;;
  cost-split)
    # Phase 1's schedule (the pin §6.3) measured: the replay's first move at 12 threads beside
    # the exterior fit's first iterate at 7 threads, 19 in all.
    mkdir -p "$out/cost_move_12_states"
    RAYON_NUM_THREADS=12 run cost_move_12 900 executed witness order2 2026093061 8 1 494208 \
      "$out/cost_move_12_best.state" "$out/cost_move_12_states" &
    RAYON_NUM_THREADS=7 run cost_represent_7 2400 executed represent order2 2026093062 8 1 2000000 \
      "$out/cost_represent_7_best.txt" &
    wait
    ;;
  # ---------------------------------------------------------------------------------------------
  # The experiments (the pin §1–§4), not launched before Astra's review. Phase 1: exp-replay (12
  # threads) beside exp-represent (7); phase 2: check-replay, then exp-coupling (12) beside the
  # continuing exp-represent; phase 3, only if a witness: check-witness, then reach (12). Each guard
  # is the projection's upper end (the pin §6.2), never raised.
  exp-replay)
    # §1: gate A's procedure re-run, every constitution's state written. Unit upper 298438 ms a
    # move; the procedure's own deadline (checked before each move) 4476570 ms leaves one move and
    # the last read inside the guard of 4820 s (projection upper 4819466 ms).
    mkdir -p "$out/states"
    RAYON_NUM_THREADS=12 run replay 4820 executed witness order2 2026093061 8 16 4476570 \
      "$out/replay_best.state" "$out/states"
    ;;
  check-replay)
    # §1 items 1 and 2: every constitution and move line against gate A's receipt (wall times
    # masked), and constitution 1's state against the saved one.
    # The persistence receipt's split (`reversed`, `uncertified`; Astra's review, October 1) is
    # new beside gate A's `fall`, its sum: masked here, and read in the record.
    mask='s/; [0-9]+ ms$//; s/, reversed: [0-9]+, uncertified: [0-9]+//g'
    diff <(sed -n '2,34p' "$gate_a/witness.txt" | sed -E "$mask") \
      <(sed -n '2,34p' "$out/replay.txt" | sed -E "$mask")
    cmp "$out/states/c1.state" "$gate_a/witness_best.state"
    echo "the replay reproduces gate A's 33 lines and its saved state"
    ;;
  exp-coupling)
    # §2: the 17 states in order. Unit upper 126822 + 3947·k ms at constitution k; the run's own
    # deadline (checked before each constitution) 2502740 ms; the guard 2693 s (projection upper
    # 2692707 ms).
    states=()
    for k in $(seq 0 16); do states+=("$k=$out/states/c$k.state"); done
    RAYON_NUM_THREADS=12 run coupling 2693 executed coupling order2 2026093061 8 2502740 "${states[@]}"
    ;;
  exp-represent)
    # §3: the exterior fit, 16 iterates. Unit upper 849557 ms an iterate (the gradients, the Gram
    # and eight trials); the run's own deadline (checked before each iterate) 12743355 ms leaves an
    # iterate, the last read and the scope read inside the guard of 13755 s (projection upper
    # 13754940 ms).
    RAYON_NUM_THREADS=7 run represent 13755 executed represent order2 2026093061 8 16 12743355 \
      "$out/represent_best.txt" 2026100101
    ;;
  check-witness)
    # §9 falsifier 5, only if a witness: its E and ρ read in a fresh process (guard 45 s: the
    # measured 44458 ms read at 12 threads, at the release's largest reading count; the process's
    # setup measured under 50 ms).
    RAYON_NUM_THREADS=12 run witness_check 45 executed replay order2 2026093061 8 \
      "witness=$out/represent_best.txt"
    # §3.3: the witness's three solved notions and landing factorial, one constitution (unit upper
    # 126822 ms at k = 0, no earlier context to retain).
    RAYON_NUM_THREADS=12 run witness_coupling 127 executed coupling order2 2026093061 8 126822 \
      "witness=$out/represent_best.txt"
    ;;
  gate-lean)
    # The Lean libraries, held to this worker's 19 processors.
    { time taskset -c 0-18 bash tools/lean_check.sh Holonics HolonicsResearch; } > "$out/gate_lean.txt" 2>&1 \
      || echo "exit $?" >> "$out/gate_lean.txt"
    ;;
  gate-tests)
    { time taskset -c 0-18 cargo test -p holonics --lib -j 19; } > "$out/gate_tests.txt" 2>&1 \
      || echo "exit $?" >> "$out/gate_tests.txt"
    ;;
  gate-replay)
    { time taskset -c 0-18 bash research/notebook/hnn_design/replay_baseline.sh; } > "$out/gate_replay.txt" 2>&1 \
      || echo "exit $?" >> "$out/gate_replay.txt"
    ;;
  *)
    echo "a run: cost-replay | cost-move | cost-coupling | cost-represent" >&2
    exit 2
    ;;
esac
