#!/usr/bin/env bash
# Gate 3 for the engine (docs/plans/THE_CONSOLIDATION.md §8 and C2, #603): parity and reproduction against the line that trains.
#
#   bash tools/gate_engine.sh LINE BIN OUT
#
# LINE is a private file of shell assignments (under `.local/`, never committed) naming the store line's inputs as its chain names them:
#   U0 S K C C2 H   the units, the store directory, the keys, the read's codec, the training codec and the held passage;
#   FROM            the saved state a lap of the line trained from, and LAP_LOG that lap's log;
#   MEAN READ_OUT   a lap's mean state and the directory its own read-cavity wrote (its cavity.tsv);
#   PLACES          the read's places (the line's read script's count).
# BIN is the field_pass build under test (release, the card's). OUT is a new scratch directory.
#
# In one hold of the card lock:
#   1. parity-store on 3 of the line's sections from FROM: every read asked of the card and of the host and compared whole
#      (STORE_PARITY_DONE ... EQUAL), and the run's STORE_SECTION lines equal to the lap's own (tools/reproduction.py);
#   2. train-store on 24 of the line's sections from FROM, the card alone: the lines equal to the lap's;
#   3. read-cavity on MEAN: its cavity.tsv equal byte for byte to the lap's own read.
# Prints GATE_ENGINE EQUAL or DIFFERS; exits 0 or 1. Parity alone cannot see a change of law made on both realizations, and the
# reproduction alone cannot see a realization that agrees with the line by luck of the sections it read, so both are run.
# Projection (November 14): parity about 70 s a section on the host's side, the training 20 s, the read 310 s; about 9 minutes, and the
# deadline 30 minutes a step.
set -u -o pipefail
[ $# -eq 3 ] || { echo "usage: bash tools/gate_engine.sh LINE BIN OUT"; exit 2; }
LINE=$1; BIN=$2; OUT=$3
# shellcheck disable=SC1090
. "$LINE"
ROOT=$(cd "$(dirname "$0")/.." && pwd)
LOCK=$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir)/../.local/gpu.lock
M="python3 -I $ROOT/tools/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
mkdir "$OUT" || exit 2
status=0
(
  flock -w 14400 9 || exit 75
  echo "# lock taken $(date -u +%H:%M:%S)"
  env -i HOME="$HOME" PATH="$PATH" $M parity timeout 1800 "$BIN" parity complete-language parity-store "$U0" "$(sha "$U0")" "$S" "$(sha "$S/STORE.tsv")" prefix "$K" "$(sha "$K")" "$C2" "$(sha "$C2")" "$H" "$(sha "$H")" 3 3 1800000 "$OUT/parity" "$FROM" "$(sha "$FROM")" > "$OUT/parity.log" 2>&1
  echo "# parity: exit $? $(date -u +%H:%M:%S)"
  env -i HOME="$HOME" PATH="$PATH" $M repro timeout 1800 "$BIN" train complete-language train-store "$U0" "$(sha "$U0")" "$S" "$(sha "$S/STORE.tsv")" prefix "$K" "$(sha "$K")" "$C2" "$(sha "$C2")" "$H" "$(sha "$H")" 24 24 1800000 "$OUT/repro" "$FROM" "$(sha "$FROM")" > "$OUT/repro.log" 2>&1
  echo "# repro: exit $? $(date -u +%H:%M:%S)"
  env -i HOME="$HOME" PATH="$PATH" $M read timeout 1800 "$BIN" train complete-language read-cavity "$U0" "$(sha "$U0")" "$S" "$(sha "$S/STORE.tsv")" "$K" "$(sha "$K")" "$C" "$(sha "$C")" "$PLACES" "$MEAN" "$(sha "$MEAN")" "$OUT/read" > "$OUT/read.log" 2>&1
  echo "# read: exit $? $(date -u +%H:%M:%S)"
) 9>"$LOCK"
grep -h "^STORE_PARITY" "$OUT/parity.log"
grep -q "^STORE_PARITY_DONE .* EQUAL$" "$OUT/parity.log" || status=1
python3 -I "$ROOT/tools/reproduction.py" "$OUT/parity.log" "$LAP_LOG" 3 --no-save || status=1
python3 -I "$ROOT/tools/reproduction.py" "$OUT/repro.log" "$LAP_LOG" 24 --no-save || status=1
if cmp "$OUT/read/cavity.tsv" "$READ_OUT/cavity.tsv"; then echo "GATE_READ cavity.tsv EQUAL"; else echo "GATE_READ cavity.tsv DIFFERS"; status=1; fi
grep -h "^MEASURE" "$OUT"/*.log
echo "GATE_ENGINE $([ $status -eq 0 ] && echo EQUAL || echo DIFFERS)"
exit $status
