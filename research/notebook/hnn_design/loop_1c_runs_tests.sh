#!/usr/bin/env bash
# Negative tests of loop_1c_runs.sh's fail-closed chain (Astra's review of 722c3334), each with its
# positive control, so no refusal passes vacuously:
#
#   bash research/notebook/hnn_design/loop_1c_runs_tests.sh
#
# 1. a replay mismatch, a replay timeout (the outer guard), a replay that panics or stops at its own
#    deadline, and a malformed full checkpoint each stop `chain-continuation` with a nonzero exit,
#    and the coupling is never launched;
# 2. `exp-coupling` refuses without a passing `check-replay`, and when a state changed since;
# 3. `exp-reach` refuses without a passing `check-witness`: an unvalidated witness (a fresh read
#    short of 64, a refused one, or no witness at all) is never stamped and launches nothing after
#    it; a witness file changed since its check refuses too;
# 4. the threads: a run past the 19-thread reservation beside a live one is refused, one within it
#    admitted; `build` is refused inside a running phase; a run refuses a binary changed since the
#    build;
# 5. `schedule` composes the chains under the same rules: a mismatched replay stops the coupling
#    and reach while the independent witness check still runs.
#
# The restore check runs the real parser (`executed restore` of the worktree's release binary, built
# by `loop_1c_runs.sh build`); every other harness mode is a stub that writes the outputs its
# scenario declares and logs its invocation, so the tests read the launcher's decisions alone, in
# seconds. Exit 0 when every test passes, 1 otherwise.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
launcher=$root/research/notebook/hnn_design/loop_1c_runs.sh
real=$root/target/release/examples/hnn_prediction
gate_a=$root/research/records/2026-09-30_STEP_1B_GATE_A_receipts
[[ -x $real ]] || { echo "the release binary is missing: bash $launcher build" >&2; exit 2; }
mkdir -p "$root/.local"
work=$(mktemp -d "$root/.local/loop_1c_tests.XXXXXX")
sleeper=
cleanup() {
  [[ -n $sleeper ]] && kill "$sleeper" 2> /dev/null || true
  rm -rf "$work"
}
trap cleanup EXIT

# The stub of hnn_prediction. Arguments as the launcher passes them: `executed <mode> …`.
stub=$work/stub
cat > "$stub" << 'STUB'
#!/usr/bin/env bash
echo "$*" >> "$STUB_LOG"
case "$2" in
  restore) exec "$REAL_BIN" "$@" ;;
  witness)
    # executed witness order2 <seed> <count> <moves> <deadline> <best> <states dir>
    states=$9
    case "${STUB_REPLAY:-match}" in
      timeout) exec sleep 30 ;;
      panic) echo "thread 'main' panicked" >&2; exit 101 ;;
      incomplete)
        sed -n '1,10p' "$GATE_A/witness.txt"
        echo "executed witness: stopped at the deadline, before move 4 (incomplete); 1 ms; resident unread"
        exit 3 ;;
    esac
    for k in $(seq 0 16); do cp "$GATE_A/witness_best.state" "$states/c$k.state"; done
    if [[ ${STUB_REPLAY:-match} == mismatch ]]; then
      sed -n '1,108p' "$GATE_A/witness.txt" | sed '4s/solved 7 of 64/solved 8 of 64/'
    else
      sed -n '1,108p' "$GATE_A/witness.txt"
    fi
    if [[ ${STUB_REPLAY:-match} == malformed ]]; then
      # E and ρ intact, the rest of the state gone: a partial remount would read it.
      head -n 122 "$GATE_A/witness_best.state" > "$states/c5.state"
    fi
    ;;
  coupling) echo "executed coupling: a stub" ;;
  represent)
    # executed represent order2 <seed> <count> <iterates> <deadline> <out> [<held-out seed>]
    head -n 122 "$GATE_A/witness_best.state" > "$8"
    if [[ ${STUB_REPRESENT:-none} == witness ]]; then
      echo "executed represent: a witness FOUND at iterate 2, trial 0: the strict test holds at all 64 decision terms of its own release; E and ρ written to $8 (a representation diagnostic, not a learning result)"
    else
      echo "executed represent: no witness found within this procedure and budget (stopped at the iterates are spent); the best own: 9 of 64, at iterate 3; the best frozen (admissible trials): None; written to $8"
    fi
    ;;
  replay)
    case "${STUB_WITNESS:-ok}" in
      ok)
        echo "  witness: solved 64 of 64 decision terms; whole sections 8 of 8 (a stub)"
        echo "  witness: admissible as a representation (the pin §3.1): a stub" ;;
      short)
        echo "  witness: solved 63 of 64 decision terms; whole sections 7 of 8 (a stub)"
        echo "  witness: admissible as a representation (the pin §3.1): a stub" ;;
      refused)
        echo "executed replay: witness, declared partial, refused: inadmissible: the entry 9 lies outside the entry box ±8"
        exit 4 ;;
    esac
    ;;
  *) echo "the stub has no mode $2" >&2; exit 2 ;;
esac
STUB
chmod +x "$stub"

failures=0
expect() {
  # expect <description> <test…>
  local description=$1
  shift
  if "$@"; then
    echo "ok    $description"
  else
    echo "FAIL  $description"
    failures=$((failures + 1))
  fi
}

fresh() {
  # A fresh artifacts directory, the stub stamped as `build` stamps the binary.
  local dir
  dir=$(mktemp -d "$work/case.XXXXXX")
  mkdir -p "$dir/stamps"
  sha256sum "$stub" > "$dir/stamps/build.ok"
  : > "$dir/stub.log"
  echo "$dir"
}

launch() {
  # launch <dir> <step> [VAR=value…]: the launcher with the stub; prints its exit status.
  local dir=$1 step=$2 status=0
  shift 2
  env LOOP_1C_OUT="$dir" LOOP_1C_BIN="${STUB_BIN:-$stub}" STUB_LOG="$dir/stub.log" REAL_BIN="$real" \
    GATE_A="$gate_a" "$@" bash "$launcher" "$step" >> "$dir/launcher.log" 2>&1 || status=$?
  echo "$status"
}

launched() {
  # launched <dir> <pattern>: how many harness invocations matched.
  grep -c -- "$2" "$1/stub.log" || true
}

is() { [[ $1 == "$2" ]]; }

echo "1. the continuation chain stops on every failure of the replay, before the coupling"

dir=$(fresh)
status=$(launch "$dir" chain-continuation STUB_REPLAY=mismatch)
expect "replay mismatch: the chain exits 10 (a check failed): $status" is "$status" 10
expect "replay mismatch: the coupling is never launched" is "$(launched "$dir" '^executed coupling ')" 0
expect "replay mismatch: the restore is never launched" is "$(launched "$dir" '^executed restore ')" 0
expect "replay mismatch: no replay stamp" test ! -e "$dir/stamps/replay.ok"
expect "replay mismatch: the difference is kept" grep -q 'solved 8 of 64' "$dir/check_replay.diff"

dir=$(fresh)
status=$(launch "$dir" chain-continuation STUB_REPLAY=timeout LOOP_1C_GUARD_CAP=2)
expect "replay timeout: the chain exits 124 (the outer guard): $status" is "$status" 124
expect "replay timeout: its receipt records the guard" grep -q '^exit 124 (124: the outer guard of 2 s)' "$dir/replay.time"
expect "replay timeout: the coupling is never launched" is "$(launched "$dir" '^executed coupling ')" 0
expect "replay timeout: no replay stamp" test ! -e "$dir/stamps/replay.ok"

dir=$(fresh)
status=$(launch "$dir" chain-continuation STUB_REPLAY=panic)
expect "replay panic: the chain exits 101: $status" is "$status" 101
expect "replay panic: the coupling is never launched" is "$(launched "$dir" '^executed coupling ')" 0

dir=$(fresh)
status=$(launch "$dir" chain-continuation STUB_REPLAY=incomplete)
expect "replay stopped at its own deadline: the chain exits 3 (incomplete): $status" is "$status" 3
expect "replay stopped at its own deadline: the coupling is never launched" is "$(launched "$dir" '^executed coupling ')" 0

dir=$(fresh)
status=$(launch "$dir" chain-continuation STUB_REPLAY=malformed)
expect "malformed full checkpoint: the chain exits 4 (the real restore refused it): $status" is "$status" 4
expect "malformed full checkpoint: the restore names c5 and refuses a partial remount" \
  grep -q '^executed restore: 5 (.*c5.state) refused: not a complete continuing state .*never read as a partial remount$' "$dir/restore.txt"
expect "malformed full checkpoint: the coupling is never launched" is "$(launched "$dir" '^executed coupling ')" 0
expect "malformed full checkpoint: no replay stamp" test ! -e "$dir/stamps/replay.ok"

dir=$(fresh)
status=$(launch "$dir" chain-continuation STUB_REPLAY=match)
expect "positive control: a replay that reproduces gate A runs the chain to its end: $status" is "$status" 0
expect "positive control: the real restore read all 17 states whole" grep -q '^executed restore: 17 states; ' "$dir/restore.txt"
expect "positive control: the coupling is launched once" is "$(launched "$dir" '^executed coupling ')" 1
expect "positive control: the coupling reads the 17 verified states" \
  is "$(grep '^executed coupling ' "$dir/stub.log" | grep -o "=$dir/states/c[0-9]*\.state" | wc -l)" 17
expect "positive control: the replay is stamped" test -s "$dir/stamps/replay.ok"
continued=$dir

echo "2. the coupling requires a verified replay"

dir=$(fresh)
status=$(launch "$dir" exp-replay STUB_REPLAY=match)
expect "the replay alone exits 0: $status" is "$status" 0
status=$(launch "$dir" exp-coupling)
expect "coupling without check-replay: refused 11: $status" is "$status" 11
expect "coupling without check-replay: never launched" is "$(launched "$dir" '^executed coupling ')" 0
status=$(launch "$dir" check-replay)
expect "check-replay passes on the reproduced replay: $status" is "$status" 0
cp "$dir/states/c3.state" "$work/c3.kept"
echo "extra" >> "$dir/states/c3.state"
status=$(launch "$dir" exp-coupling)
expect "coupling after a verified state changed: refused 11: $status" is "$status" 11
expect "coupling after a verified state changed: never launched" is "$(launched "$dir" '^executed coupling ')" 0
cp "$work/c3.kept" "$dir/states/c3.state"
status=$(launch "$dir" exp-coupling)
expect "positive control: the coupling launches on the verified states: $status" is "$status" 0
expect "positive control: launched once" is "$(launched "$dir" '^executed coupling ')" 1

echo "3. reach requires a validated witness (and the replay)"

dir=$continued
: > "$dir/stub.log"
status=$(launch "$dir" exp-reach)
expect "reach without check-witness: refused 11: $status" is "$status" 11

status=$(launch "$dir" exp-represent STUB_REPRESENT=none)
expect "a search without a witness exits 0: $status" is "$status" 0
status=$(launch "$dir" check-witness)
expect "check-witness without a witness: refused 10: $status" is "$status" 10
expect "check-witness without a witness: no fresh read launched" is "$(launched "$dir" '^executed replay ')" 0

status=$(launch "$dir" exp-represent STUB_REPRESENT=witness)
expect "a search claiming a witness exits 0: $status" is "$status" 0
status=$(launch "$dir" check-witness STUB_WITNESS=short)
expect "a witness whose fresh read solves 63 of 64: refused 10: $status" is "$status" 10
expect "  its fresh read was made, partial declared" is "$(launched "$dir" '^executed replay .*witness=partial:')" 1
expect "  no witness stamp" test ! -e "$dir/stamps/witness.ok"
expect "  its coupling read never launched" is "$(launched "$dir" '^executed coupling .*witness=partial:')" 0
status=$(launch "$dir" exp-reach)
expect "  reach on the unvalidated witness: refused 11: $status" is "$status" 11

status=$(launch "$dir" check-witness STUB_WITNESS=refused)
expect "a witness the fresh read refuses (inadmissible): exits 4: $status" is "$status" 4
expect "  no witness stamp" test ! -e "$dir/stamps/witness.ok"
status=$(launch "$dir" exp-reach)
expect "  reach: refused 11: $status" is "$status" 11

status=$(launch "$dir" check-witness STUB_WITNESS=ok)
expect "positive control: a witness that reproduces is validated: $status" is "$status" 0
expect "  stamped" test -s "$dir/stamps/witness.ok"
expect "  its coupling read launched once" is "$(launched "$dir" '^executed coupling .*witness=partial:')" 1
status=$(launch "$dir" exp-reach)
expect "  reach passes both checks and stops at 13 (not built): $status" is "$status" 13
expect "  its refusal says reach is not built" grep -q 'reach is not built' "$dir/launcher.log"
echo "E 1 1" >> "$dir/represent_best.txt"
status=$(launch "$dir" exp-reach)
expect "reach after the validated witness file changed: refused 11: $status" is "$status" 11

status=$(launch "$dir" exp-represent STUB_REPRESENT=witness)
expect "a new search removes the old witness stamp" test ! -e "$dir/stamps/witness.ok"
status=$(launch "$dir" exp-reach)
expect "  reach after a new search, before its check: refused 11: $status" is "$status" 11

echo "4. the thread reservation and the build staging"

dir=$(fresh)
mkdir -p "$dir/threads"
sleep 60 &
sleeper=$!
echo "$sleeper 12" > "$dir/threads/phase"
echo "exit 0 (124: the outer guard of 4954 s)" > "$dir/replay.time"
status=$(launch "$dir" exp-replay STUB_REPLAY=match)
expect "a 12-thread run beside a live 12: refused 12: $status" is "$status" 12
expect "  never launched" is "$(launched "$dir" '^executed witness ')" 0
expect "  an earlier run's exit-0 receipt is removed, never left for a check" test ! -e "$dir/replay.time"
status=$(launch "$dir" exp-represent STUB_REPRESENT=none)
expect "positive control: a 7-thread run beside a live 12 (19 in all) is admitted: $status" is "$status" 0
expect "  launched once" is "$(launched "$dir" '^executed represent ')" 1
status=$(launch "$dir" build)
expect "build inside a running phase: refused 12: $status" is "$status" 12
kill "$sleeper" 2> /dev/null || true
wait "$sleeper" 2> /dev/null || true
sleeper=
status=$(launch "$dir" exp-replay STUB_REPLAY=match)
expect "positive control: the 12-thread run once the phase ended: $status" is "$status" 0

dir=$(fresh)
cp "$stub" "$dir/stub"
sha256sum "$dir/stub" > "$dir/stamps/build.ok"
echo "# changed after the build" >> "$dir/stub"
status=$(STUB_BIN=$dir/stub launch "$dir" exp-replay STUB_REPLAY=match)
expect "a binary changed since the build: refused 11: $status" is "$status" 11
expect "  never launched" is "$(wc -l < "$dir/stub.log")" 0
rm -f "$dir/stamps/build.ok"
status=$(launch "$dir" exp-replay STUB_REPLAY=match)
expect "no verified build: refused 11: $status" is "$status" 11

echo "5. the schedule composes the chains under the same rules"

dir=$(fresh)
status=$(launch "$dir" schedule STUB_REPLAY=match STUB_REPRESENT=none)
expect "positive control: the schedule without a witness exits 0: $status" is "$status" 0
expect "  the coupling launched once" is "$(launched "$dir" '^executed coupling ')" 1
expect "  the search launched once" is "$(launched "$dir" '^executed represent ')" 1
expect "  no witness check launched" is "$(launched "$dir" '^executed replay ')" 0

dir=$(fresh)
status=$(launch "$dir" schedule STUB_REPLAY=mismatch STUB_REPRESENT=witness STUB_WITNESS=ok)
expect "a schedule whose replay mismatches exits 10 though its witness validates: $status" is "$status" 10
expect "  the coupling is never launched" is "$(launched "$dir" '^executed coupling [^w]*$')" 0
expect "  the witness, independent of the replay, is checked" test -s "$dir/stamps/witness.ok"
expect "  reach is refused for the unverified replay" grep -q 'check-replay has not passed' "$dir/launcher.log"

echo
if (( failures == 0 )); then
  echo "loop_1c_runs_tests: every test passed"
else
  echo "loop_1c_runs_tests: $failures FAILED"
  exit 1
fi
