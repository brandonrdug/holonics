#!/usr/bin/env bash
# Loop 1c's declared runs (THE_REBUILD U6, step 1, loop 1c; the pin
# research/records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md).
#
#   bash research/notebook/hnn_design/loop_1c_runs.sh <step>
#
# Fail-closed (Astra's review of 722c3334; its negative tests are loop_1c_runs_tests.sh):
#
# - Every run's exit propagates. A run that fails, is refused, stops incomplete (the harness's own
#   deadline or a pinned bound: exit 3) or reaches its outer guard (124) stops the step and every
#   step after it with that status. Nothing is waited out or retried, and no guard is raised.
# - A consumer runs only after the verified success of what it reads: a check step that passes
#   writes a stamp (`<out>/stamps/<name>.ok`, the sha256 of every artifact it verified and of the
#   binary that read them), and the consumer refuses unless the stamp exists and every listed file
#   is unchanged. `exp-coupling` requires `check-replay`; `exp-reach` requires `check-replay` and
#   `check-witness`. Only a passing check writes a stamp; a producing run removes its consumers'.
# - A checkpoint mismatch fails, it does not warn: `check-replay` restores all 17 states whole
#   (`executed restore`: parsed, continued onto the declared opening, written back byte for byte)
#   before the coupling may launch, and the harness itself refuses a complete state that does not
#   restore whole; it never falls back to a partial remount (only `label=partial:<file>`, declared,
#   remounts E and ρ alone).
# - Threads: at most 19 (the host's 24 less Codex's reserved 5). Each run reserves its declared
#   threads in a ledger (`<out>/threads/`, one `pid threads` file a live run) and is refused past
#   19 with the live runs. The binary is built once, by `build`, before the schedule and alone
#   (`-j 19`, refused while any run of this loop is live); every run verifies the binary against
#   that build's stamp and never builds.
#
# Exit statuses: 0 success; 2 usage; 10 a check failed; 11 a dependency not verified (no stamp, or
# its artifacts or the binary changed since); 12 the thread reservation or the build staging
# refused; 13 reach is not built; 124 a run's outer guard; any other: the harness's own (3
# incomplete, 4 a refused input, 5 an identity mismatch against gate A's receipt, 101 a panic).
#
# Every run's artifacts are in `<out>` (the worktree's `.local/1c/`): `<name>.txt` its stdout,
# `<name>.err` its stderr, `<name>.time` its wall and CPU times and exit (the peak resident set is
# the harness's own last line). For the launcher's tests only: LOOP_1C_OUT and LOOP_1C_BIN redirect
# the artifacts and the binary, and LOOP_1C_GUARD_CAP lowers every guard to at most that many
# seconds (it can never raise one).
#
# The steps:
#   build                      the release binary, once, alone (-j 19), and its stamp
#   cost-replay, check-cost-replay, cost-move, check-cost-move, cost-coupling, cost-coupling-12,
#   cost-represent, cost-split the development cost reads (the pin §6.1)
#   exp-replay, check-replay, exp-coupling, exp-represent, check-witness, exp-reach
#                              the experiments and their checks (the pin §1–§4, §6.2–§6.3)
#   exp-c2, check-c2           the c2 diagnostic (gate A's constitution 1 resumed by one native
#                              update, then the re-reads at constitution 2), and its check and stamp
#   chain-continuation         exp-replay, then check-replay, then exp-coupling
#   schedule                   the pin §6.3 whole: chain-continuation beside exp-represent; then,
#                              only if a witness, check-witness and exp-reach
#   gate-tests, gate-replay, gate-lean
#                              the gates, each holding all 19 threads
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
out=${LOOP_1C_OUT:-.local/1c}
bin=${LOOP_1C_BIN:-target/release/examples/hnn_prediction}
gate_a=research/records/2026-09-30_STEP_1B_GATE_A_receipts
reservation=19
stamps=$out/stamps
ledger=$out/threads
mkdir -p "$out" "$stamps" "$ledger"
if [[ -n ${LOOP_1C_GUARD_CAP:-} && ! ${LOOP_1C_GUARD_CAP} =~ ^[1-9][0-9]*$ ]]; then
  echo "loop_1c_runs: LOOP_1C_GUARD_CAP must be a positive count of seconds" >&2
  exit 2
fi

refuse() {
  # refuse <status> <reason>: the step fails, and with it every step after it.
  local status=$1
  shift
  echo "loop_1c_runs: REFUSED (exit $status): $*" >&2
  exit "$status"
}

live_threads() {
  # The threads reserved by this loop's live runs; a dead run's entry is removed.
  local total=0 pid threads entry
  for entry in "$ledger"/*; do
    [[ -e $entry ]] || continue
    read -r pid threads < "$entry" || continue
    if kill -0 "$pid" 2> /dev/null; then
      total=$((total + threads))
    else
      rm -f "$entry"
    fi
  done
  echo "$total"
}

reserve() {
  # reserve <name> <threads>: refused past the reservation with the live runs, or when a run of the
  # same name is live. The entry lives with the process that holds it.
  local name=$1 threads=$2 lock live
  exec {lock}> "$out/threads.lock"
  flock "$lock"
  live=$(live_threads)
  if [[ -e $ledger/$name ]]; then
    flock -u "$lock"
    refuse 12 "a run named $name is live"
  fi
  if (( live + threads > reservation )); then
    flock -u "$lock"
    refuse 12 "$name's $threads threads beside the $live live would pass the reservation of $reservation"
  fi
  echo "$BASHPID $threads" > "$ledger/$name"
  flock -u "$lock"
  exec {lock}>&-
}

release() {
  rm -f "$ledger/$1"
}

verify_build() {
  [[ -f $stamps/build.ok ]] || refuse 11 "no verified build: run \`build\` first, alone, before the schedule"
  sha256sum --check --status "$stamps/build.ok" 2> /dev/null \
    || refuse 11 "the binary differs from the verified build: the binary is built once, before the schedule"
}

stamp() {
  # stamp <name> <files…>: written only by a passing check: the sha256 of every artifact it verified
  # and of the binary that read them.
  local name=$1
  shift
  sha256sum "$bin" "$@" > "$stamps/$name.ok.partial"
  mv "$stamps/$name.ok.partial" "$stamps/$name.ok"
}

require() {
  # require <name> <what>: refused unless the check passed and nothing it verified has changed.
  local name=$1
  shift
  [[ -f $stamps/$name.ok ]] || refuse 11 "$* has not passed (no stamp $stamps/$name.ok)"
  sha256sum --check --status "$stamps/$name.ok" 2> /dev/null \
    || refuse 11 "an artifact $* verified, or the binary, has changed since it passed"
}

run() {
  # run <name> <threads> <guard s> <args…>: the binary at <threads> rayon threads under the outer
  # guard; returns the run's exit (124: the guard). Never builds.
  local name=$1 threads=$2 guard=$3
  shift 3
  # An earlier run's receipts go first, so a run refused below never leaves an older `exit 0`.
  rm -f "$out/$name.txt" "$out/$name.err" "$out/$name.time"
  verify_build
  if [[ -n ${LOOP_1C_GUARD_CAP:-} ]] && (( LOOP_1C_GUARD_CAP < guard )); then
    guard=$LOOP_1C_GUARD_CAP
  fi
  reserve "$name" "$threads"
  local TIMEFORMAT="wall %R s, user %U s, system %S s, cpu %P percent"
  local status=0
  { time RAYON_NUM_THREADS=$threads timeout "$guard" "$bin" "$@" > "$out/$name.txt" 2> "$out/$name.err"; } \
    2> "$out/$name.time" || status=$?
  release "$name"
  echo "exit $status (124: the outer guard of $guard s)" >> "$out/$name.time"
  return "$status"
}

hold() {
  # hold <name> <command…>: a gate holding all 19 threads (refused beside any live run).
  local name=$1
  shift
  reserve "$name" "$reservation"
  local status=0
  { time taskset -c 0-18 "$@"; } > "$out/$name.txt" 2>&1 || status=$?
  release "$name"
  echo "exit $status" >> "$out/$name.txt"
  return "$status"
}

exited_zero() {
  [[ -f $out/$1.time ]] && tail -n 1 "$out/$1.time" | grep -q '^exit 0 '
}

states() {
  local k
  for k in $(seq 0 16); do echo "$k=$out/states/c$k.state"; done
}

# -------------------------------------------------------------------------------------------------
# the build, staged before the schedule

build() {
  # All 19 threads, so refused while any run of this loop is live: never inside a running phase.
  reserve build "$reservation"
  [[ -z ${LOOP_1C_BIN:-} ]] || refuse 2 "build stamps the worktree's release binary only (LOOP_1C_BIN is set)"
  local status=0
  cargo build --release -q -j "$reservation" -p holonics --example hnn_prediction || status=$?
  release build
  (( status == 0 )) || refuse "$status" "the build failed"
  sha256sum "$bin" > "$stamps/build.ok.partial"
  mv "$stamps/build.ok.partial" "$stamps/build.ok"
  echo "built and stamped: $(cat "$stamps/build.ok")"
}

# -------------------------------------------------------------------------------------------------
# the experiments (the pin §1–§4); each guard is the projection's upper end (the pin §6.2)

exp_replay() {
  # §1: gate A's procedure re-run at 12 threads, every constitution's state written. Unit upper
  # 306738 ms a move (the larger of the two measured reads, §6.2′); the procedure's own deadline
  # (checked before each move) 4601070 ms leaves one move and the last read (45592 ms) inside the
  # guard of 4954 s (projection upper 4953400 ms).
  rm -f "$stamps/replay.ok"
  rm -rf "$out/states"
  mkdir -p "$out/states"
  run replay 12 4954 executed witness order2 2026093061 8 16 4601070 \
    "$out/replay_best.state" "$out/states" \
    || refuse $? "the replay failed, was refused, stopped incomplete or reached its guard"
}

check_replay() {
  # §1 items 1–3: the replay exited 0 and spent its 16 moves; its constitution and move lines equal
  # gate A's receipt (wall times masked; the persistence split of Astra's review, beside gate A's
  # `fall`, masked); c1.state is byte-identical to gate A's saved state; and every one of the 17
  # states restores whole onto the declared opening and writes back to its own text. Passing, it
  # stamps the replay's listing and states.
  exited_zero replay || refuse 10 "the replay did not exit 0"
  local mask='s/; [0-9]+ ms$//; s/, reversed: [0-9]+, uncertified: [0-9]+//g'
  diff <(sed -n '2,34p' "$gate_a/witness.txt" | sed -E "$mask") \
    <(sed -n '2,34p' "$out/replay.txt" | sed -E "$mask") > "$out/check_replay.diff" \
    || refuse 10 "the replay's constitution and move lines differ from gate A's ($out/check_replay.diff)"
  grep -q '^executed witness: stopped at the moves are spent; ' "$out/replay.txt" \
    || refuse 10 "the replay did not spend its 16 moves"
  local k files=("$out/replay.txt")
  for k in $(seq 0 16); do
    [[ -s $out/states/c$k.state ]] || refuse 10 "the state c$k.state is missing"
    files+=("$out/states/c$k.state")
  done
  cmp -s "$out/states/c1.state" "$gate_a/witness_best.state" \
    || refuse 10 "c1.state differs from gate A's saved state"
  # The restore, no reading made: 17 copies of gate A's saved state measured at 206 ms wall (186 ms
  # the process's own) at 1 thread; guard 5 s.
  mapfile -t arms < <(states)
  run restore 1 5 executed restore "${arms[@]}" \
    || refuse $? "a state does not restore whole and write back to its own text ($out/restore.txt)"
  stamp replay "${files[@]}"
  echo "check-replay: gate A's 33 lines reproduced, c1.state is gate A's saved state, and all 17 states restore whole and write back; stamped"
}

exp_coupling() {
  # §2: the 17 states in order, at 12 threads, only after a verified replay. Unit upper
  # 126822 + 3947·k ms at constitution k; the run's own deadline (checked before each constitution)
  # 2502740 ms; the guard 2693 s (projection upper 2692707 ms). Past 6 events a constitution the
  # harness stops incomplete (the pin §6.2).
  require replay "check-replay"
  mapfile -t arms < <(states)
  run coupling 12 2693 executed coupling order2 2026093061 8 2502740 "${arms[@]}" \
    || refuse $? "the coupling failed, was refused, stopped incomplete or reached its guard"
}

exp_represent() {
  # §3: the exterior fit at 7 threads, 16 iterates. Unit upper 849557 ms an iterate (the gradients,
  # the Gram and eight trials); the run's own deadline (checked before each iterate) 12743355 ms
  # leaves an iterate, the last read and the scope read (94874 ms each, §6.2′) inside the guard of
  # 13783 s (projection
  # upper 13754940 ms).
  rm -f "$stamps/witness.ok"
  run represent 7 13783 executed represent order2 2026093061 8 16 12743355 \
    "$out/represent_best.txt" 2026100101 \
    || refuse $? "the representation search failed, was refused, stopped incomplete or reached its guard"
}

check_witness() {
  # §9 falsifier 5, only if a witness: the search exited 0 with a witness; its E and ρ, declared
  # partial, read in a fresh process at 12 threads (guard 46 s: the larger measured read, 45592 ms, §6.2′) must be
  # admissible and certified, and solve all 64 decision terms. Passing, it stamps the witness; then
  # its coupling reads (§3.3), one constitution (unit upper 126822 ms at k = 0).
  exited_zero represent || refuse 10 "the representation search did not exit 0"
  grep -q '^executed represent: a witness FOUND at ' "$out/represent.txt" \
    || refuse 10 "the representation search found no witness: check-witness and reach are not launched"
  [[ -s $out/represent_best.txt ]] || refuse 10 "the witness's file is missing"
  run witness_check 12 46 executed replay order2 2026093061 8 "witness=partial:$out/represent_best.txt" \
    || refuse $? "the witness's fresh read failed, was refused or reached its guard: the claim is withdrawn"
  grep -q '^  witness: solved 64 of 64 decision terms; ' "$out/witness_check.txt" \
    || refuse 10 "the witness's fresh read does not solve all 64 decision terms: the claim is withdrawn"
  grep -q '^  witness: admissible as a representation ' "$out/witness_check.txt" \
    || refuse 10 "the witness's fresh read printed no admissibility: the claim is withdrawn"
  stamp witness "$out/represent.txt" "$out/represent_best.txt" "$out/witness_check.txt"
  require witness "check-witness"
  run witness_coupling 12 127 executed coupling order2 2026093061 8 126822 \
    "witness=partial:$out/represent_best.txt" \
    || refuse $? "the witness's coupling reads failed, were refused, stopped incomplete or reached their guard"
  echo "check-witness: the witness reproduces in a fresh process, admissible and certified, all 64 solved; stamped; its coupling read"
}

exp_reach() {
  # §4: reach reads the replay's states and the witness, so it requires both checks. It is not built
  # (the pin §8): built only once a witness exists, against the law the pin fixes; 12 threads, guard
  # 219 s (projection upper 218586 ms).
  require replay "check-replay"
  require witness "check-witness"
  refuse 13 "reach is not built (the pin §4, §8): the witness and the replay are verified; build reach against the pin's law, its first constitution its own development read"
}

exp_c2() {
  # The c2 diagnostic (`executed resume-coupling`, narrowed by Astra's review of the c2 consumer:
  # the native order only; the move's own reading of its successor reused, never re-released; the
  # successor and its contexts captured before any diagnostic read). Gate A's saved constitution 1
  # restored whole; one native update at 12 threads on the batch gate A's move 1 read; the identity
  # against gate A's receipt (the harness exits 5 on a mismatch, reading nothing further); then the
  # 7 re-reads at constitution 2, at most 7 admitted (past it, exit 3). The harness stops the move
  # itself past 210494 ms (gate A's move 1, 145447 ms at 24 threads, times move 0's measured
  # 159075/109917 at 12 threads over 24), exit 3.
  # The outer guard of 606 s is the primary's projection for the broader three-order coupling read
  # (the move 210494, the releases 82983 · 7/2, the events 13093 · 7/5 · 7/2, the restore under
  # 40000: 605091 ms): a cross-state, cross-thread-count projection, not a demonstrated upper bound.
  # The narrowed operation's own budget, derived from its call counts, is stated in its record for
  # review; no guard is changed here.
  rm -f "$stamps/c2.ok"
  rm -rf "$out/c2_capture"
  mkdir -p "$out/c2_capture"
  run c2 12 606 executed resume-coupling order2 2026093061 8 \
    "$gate_a/witness_best.state" "$gate_a/witness.txt" 210494 "$out/c2_capture" \
    || refuse $? "the c2 diagnostic failed, was refused, stopped at an identity mismatch, stopped incomplete or reached its guard"
  check_c2
}

check_c2() {
  # Beside the harness's own gates, read from its listing: the run exited 0; constitution 1's line,
  # move 1's line and constitution 2's line equal gate A's (wall times and the persistence split
  # masked); the persistence reads at constitution 2 are gate A's move-2 tuple with none refused;
  # the run completed; the capture holds constitution 2's state and contexts. Passing, it stamps the
  # listing and the capture.
  exited_zero c2 || refuse 10 "the c2 diagnostic did not exit 0"
  local mask='s/; [0-9]+ ms$//; s/, reversed: [0-9]+, uncertified: [0-9]+//g'
  local lines='^(  constitution 1 \(before move 1\)|    move 1|  constitution 2 \(before move 2\)): '
  diff <(grep -E "$lines" "$gate_a/witness.txt" | sed -E "$mask") \
    <(grep -E "$lines" "$out/c2.txt" | sed -E "$mask") > "$out/check_c2.diff" \
    || refuse 10 "the c2 diagnostic's move and constitution lines differ from gate A's ($out/check_c2.diff)"
  local tuple
  tuple=$(grep '^    move 2: ' "$gate_a/witness.txt" | grep -o 'Persistence { [^}]*' | sed 's/ $//')
  [[ -n $tuple ]] || refuse 10 "gate A's receipt holds no persistence reads at constitution 2"
  grep -qF "  persistence at constitution 2: $tuple, reversed: " "$out/c2.txt" \
    || refuse 10 "the persistence reads at constitution 2 are not gate A's ($tuple)"
  grep -qE '^  persistence at constitution 2: .* \}; refused 0; ' "$out/c2.txt" \
    || refuse 10 "a re-read at constitution 2 was refused"
  grep -q '^executed resume-coupling: complete; ' "$out/c2.txt" || refuse 10 "the c2 diagnostic did not complete"
  [[ -s $out/c2_capture/c2.state && -s $out/c2_capture/c2_contexts.txt ]] \
    || refuse 10 "the capture of constitution 2 is missing"
  stamp c2 "$out/c2.txt" "$out/c2_capture/c2.state" "$out/c2_capture/c2_contexts.txt"
  echo "check-c2: gate A's move 1 and constitution 2 reproduced, its persistence reads at constitution 2 read, the capture kept; stamped"
}

chain_continuation() {
  exp_replay
  check_replay
  exp_coupling
}

schedule() {
  # The pin §6.3: the continuation chain (12 threads) beside the fit (7), 19 in all; then, only if a
  # witness, its check and reach (12 each), after both: the coupling's 12 and the check's 12 would
  # pass the reservation together. Each exit is reported; the first nonzero is the schedule's.
  chain_continuation &
  local continuation=$!
  exp_represent &
  local representation=$!
  local continued=0 represented=0 witnessed=0
  wait "$continuation" || continued=$?
  wait "$representation" || represented=$?
  echo "schedule: the continuation chain exit $continued, the representation search exit $represented" >&2
  if (( represented == 0 )) && grep -q '^executed represent: a witness FOUND at ' "$out/represent.txt"; then
    ( check_witness; exp_reach ) || witnessed=$?
    echo "schedule: check-witness and reach exit $witnessed" >&2
  else
    echo "schedule: no witness: check-witness and reach are not launched" >&2
  fi
  for status in "$continued" "$represented" "$witnessed"; do
    (( status == 0 )) || exit "$status"
  done
}

# -------------------------------------------------------------------------------------------------
# the development cost reads (the pin §6.1), each at its declared threads

cost_split() {
  # Phases 1 and 2 measured as scheduled (the pin §6.3): the replay's first move at 12 threads beside
  # the exterior fit's first iterate at 7, 19 in all; when the move ends, one constitution's
  # coupling reads at 12 beside the continuing fit.
  rm -rf "$out/cost_move_12_states"
  mkdir -p "$out/cost_move_12_states"
  run cost_move_12 12 900 executed witness order2 2026093061 8 1 494208 \
    "$out/cost_move_12_best.state" "$out/cost_move_12_states" &
  local move=$!
  run cost_represent_7 7 2400 executed represent order2 2026093062 8 1 2000000 \
    "$out/cost_represent_7_best.txt" &
  local fit=$!
  local moved=0 coupled=0 fitted=0
  wait "$move" || moved=$?
  if (( moved == 0 )); then
    run cost_coupling_12 12 1800 executed coupling order2 2026093062 8 1200000 opening=opening || coupled=$?
  fi
  wait "$fit" || fitted=$?
  (( moved == 0 )) || refuse "$moved" "the move's cost read failed or reached its guard"
  (( coupled == 0 )) || refuse "$coupled" "the coupling's cost read failed, stopped incomplete or reached its guard"
  (( fitted == 0 )) || refuse "$fitted" "the fit's cost read failed or reached its guard"
}

case "${1:-}" in
  build) build ;;
  cost-replay)
    run cost_replay 19 600 executed replay order2 2026093061 8 \
      "constitution 1 (before move 1)=$gate_a/witness_best.state" \
      || refuse $? "the cost read failed or reached its guard"
    ;;
  check-cost-replay)
    # The restored state's reading against gate A's receipt: its summary line (the wall time
    # masked) and its 64 decision terms whole (with the 8 requests' release lines).
    exited_zero cost_replay || refuse 10 "the cost read did not exit 0"
    mask='s/; [0-9]+ ms$//'
    diff <(sed -n '4p' "$gate_a/witness.txt" | sed -E "$mask") \
      <(sed -n '2p' "$out/cost_replay.txt" | sed -E "$mask") || refuse 10 "the summary line differs"
    diff <(sed -n '36,107p' "$gate_a/witness.txt") <(sed -n '3,74p' "$out/cost_replay.txt") \
      || refuse 10 "the 72 term lines differ"
    grep -q "identical to its file" "$out/cost_replay.err" || refuse 10 "no write-back identity"
    echo "the restored state's reading matches gate A's receipt (1 summary line, 72 term lines), and the state writes back to its file"
    ;;
  cost-move)
    rm -rf "$out/cost_move_states"
    mkdir -p "$out/cost_move_states"
    run cost_move 19 900 executed witness order2 2026093061 8 1 494208 \
      "$out/cost_move_best.state" "$out/cost_move_states" \
      || refuse $? "the cost read failed or reached its guard"
    ;;
  check-cost-move)
    # Gate A's first native move replayed: its constitution and move lines (wall times masked),
    # constitution 1's reading (its label masked), and the written state against the saved one.
    exited_zero cost_move || refuse 10 "the cost read did not exit 0"
    mask='s/; [0-9]+ ms$//; s/, reversed: [0-9]+, uncertified: [0-9]+//g; s/constitution 1 \((before move 1|after the last move)\)/constitution 1/'
    diff <(sed -n '2,4p' "$gate_a/witness.txt" | sed -E "$mask") \
      <(sed -n '2,4p' "$out/cost_move.txt" | sed -E "$mask") || refuse 10 "the move's lines differ"
    cmp "$out/cost_move_states/c1.state" "$gate_a/witness_best.state" || refuse 10 "c1.state differs"
    echo "gate A's first move replays exactly: 3 lines, and constitution 1's complete continuing state is byte-identical to gate A's saved state"
    ;;
  cost-coupling)
    run cost_coupling 19 1800 executed coupling order2 2026093062 8 1200000 opening=opening \
      || refuse $? "the cost read failed, stopped incomplete or reached its guard"
    ;;
  cost-coupling-12)
    # Phase 2's schedule: one constitution's coupling reads at 12 threads, read while the exterior
    # fit holds its 7 (launch it while `cost-split`'s fit runs).
    run cost_coupling_12 12 1800 executed coupling order2 2026093062 8 1200000 opening=opening \
      || refuse $? "the cost read failed, stopped incomplete or reached its guard"
    ;;
  cost-represent)
    run cost_represent 19 1800 executed represent order2 2026093062 8 1 1200000 \
      "$out/cost_represent_best.txt" \
      || refuse $? "the cost read failed, stopped incomplete or reached its guard"
    ;;
  cost-split) cost_split ;;
  exp-replay) exp_replay ;;
  check-replay) check_replay ;;
  exp-coupling) exp_coupling ;;
  exp-represent) exp_represent ;;
  check-witness) check_witness ;;
  exp-reach) exp_reach ;;
  exp-c2) exp_c2 ;;
  check-c2) check_c2 ;;
  chain-continuation) chain_continuation ;;
  schedule) schedule ;;
  gate-tests)
    hold gate_tests cargo test -p holonics --lib -j "$reservation" || refuse $? "the library tests failed"
    ;;
  gate-replay)
    hold gate_replay bash research/notebook/hnn_design/replay_baseline.sh || refuse $? "the baseline replay failed"
    ;;
  gate-lean)
    hold gate_lean bash tools/lean_check.sh Holonics HolonicsResearch || refuse $? "the Lean build failed"
    ;;
  *)
    echo "a step: build | cost-replay | check-cost-replay | cost-move | check-cost-move | cost-coupling | cost-coupling-12 | cost-represent | cost-split | exp-replay | check-replay | exp-coupling | exp-represent | check-witness | exp-reach | exp-c2 | check-c2 | chain-continuation | schedule | gate-tests | gate-replay | gate-lean" >&2
    exit 2
    ;;
esac
