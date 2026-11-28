#!/usr/bin/env bash
# Gate 3 for the engine (docs/plans/THE_CONSOLIDATION.md §8 and C2, #603): parity and reproduction against the line that trains.
#
#   bash tools/gate_engine.sh LINE BIN OUT
#
# LINE is a private file of shell assignments (under `.local/`, never committed) naming the store line's inputs as its chain names them:
#   U0 S K C C2 H   the units, the store directory, the keys, the read's codec, the training codec and the held passage;
#   FROM            the saved state a lap of the line trained from, and LAP_LOG that lap's log;
#   MEAN READ_OUT   a lap's mean state and the directory its own read-cavity wrote (its cavity.tsv);
#   PLACES          the read's places (the line's read script's count);
#   TRAINS          the state the line trains now (its last lap's end, or the state its running arm trained from);
#   PARITY_FROM     optional: the state the parity reads, carrying every part of TRAINS (default FROM), with PARITY_S and PARITY_C2
#                   its store and training codec (default S and C2) and PARITY_LAP_LOG the log of a lap that trained from it.
# BIN is the athena build under test (release, the card's). OUT is a new scratch directory.
#
# Beside whatever else the card runs (Brandon, November 15 16:20: only a timing hold takes the card alone; a gate checks bits, which
# every sum of the engine, met at one grain and released once, makes the same on any schedule, and each run sizes its batches from the card memory free when it opens):
#   0. PARITY_FROM carries every part TRAINS does (tools/state_families.py: the carry, the opening, the mark, the fades, the level, its
#      units and the rest of the declaration's words), or the gate fails before the card runs;
#   1. parity-store on 3 of the line's sections from PARITY_FROM: every read asked of the card and of the host and compared whole
#      (STORE_PARITY_DONE ... EQUAL), and the run's STORE_SECTION lines equal to the lap's own (tools/reproduction.py) where a lap trained
#      from that state (FROM's, or PARITY_LAP_LOG); otherwise the 24 sections of step 2 are the reproduction;
#   2. train-store on 24 of the line's sections from FROM, the card alone: the lines equal to the lap's;
#   3. read-cavity on MEAN: its cavity.tsv equal byte for byte to the lap's own read.
# Why the parity reads its own state (November 28, the fade's parity): from November 24 the line trained the rings' fades while gate 3's
# parity read LINE_W109's state, whose declaration held none, so no gate compared the card's fade covector with the host's; on W134's
# state it read about 2.5% under the host's (the opening's comparison's share of it entered the card's covector once where each of a
# marked field's two reads returns it). A reproduction needs a lap that trained from its state, and a parity needs every part the line
# trains, so the two may read two states.
# Prints GATE_ENGINE EQUAL or DIFFERS; exits 0 or 1. Parity alone cannot see a change of law made on both realizations, and the
# reproduction alone cannot see a realization that agrees with the line by luck of the sections it read, so both are run.
# Projection (November 14): parity about 70 s a section on the host's side, the training 20 s, the read 310 s; about 9 minutes, and the
# deadline 30 minutes a step. On W134's state (November 28) the parity's host side took 272 s a section, 14 minutes for its 3.
set -u -o pipefail
[ $# -eq 3 ] || { echo "usage: bash tools/gate_engine.sh LINE BIN OUT"; exit 2; }
LINE=$1; BIN=$2; OUT=$3
# shellcheck disable=SC1090
. "$LINE"
ROOT=$(cd "$(dirname "$0")/.." && pwd)
M="python3 -I $ROOT/tools/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
PARITY_FROM=${PARITY_FROM:-$FROM}; PARITY_S=${PARITY_S:-$S}; PARITY_C2=${PARITY_C2:-$C2}
if [ "$PARITY_FROM" = "$FROM" ]; then PARITY_LAP_LOG=${PARITY_LAP_LOG:-$LAP_LOG}; else PARITY_LAP_LOG=${PARITY_LAP_LOG:-}; fi
[ -n "${TRAINS:-}" ] || { echo "GATE_PARITY_FAMILIES refused: the LINE names no TRAINS (the state the line trains now)"; echo "GATE_ENGINE DIFFERS"; exit 1; }
python3 -I "$ROOT/tools/state_families.py" --covers "$PARITY_FROM" "$TRAINS" || { echo "GATE_ENGINE DIFFERS"; exit 1; }
mkdir "$OUT" || exit 2
status=0
(
  echo "# gate begun $(date -u +%H:%M:%S)"
  env -i HOME="$HOME" PATH="$PATH" $M parity timeout 1800 "$BIN" parity complete-language parity-store "$U0" "$(sha "$U0")" "$PARITY_S" "$(sha "$PARITY_S/STORE.tsv")" prefix "$K" "$(sha "$K")" "$PARITY_C2" "$(sha "$PARITY_C2")" "$H" "$(sha "$H")" 3 3 1800000 "$OUT/parity" "$PARITY_FROM" "$(sha "$PARITY_FROM")" > "$OUT/parity.log" 2>&1
  echo "# parity: exit $? $(date -u +%H:%M:%S)"
  env -i HOME="$HOME" PATH="$PATH" $M repro timeout 1800 "$BIN" train complete-language train-store "$U0" "$(sha "$U0")" "$S" "$(sha "$S/STORE.tsv")" prefix "$K" "$(sha "$K")" "$C2" "$(sha "$C2")" "$H" "$(sha "$H")" 24 24 1800000 "$OUT/repro" "$FROM" "$(sha "$FROM")" > "$OUT/repro.log" 2>&1
  echo "# repro: exit $? $(date -u +%H:%M:%S)"
  env -i HOME="$HOME" PATH="$PATH" $M read timeout 1800 "$BIN" train complete-language read-cavity "$U0" "$(sha "$U0")" "$S" "$(sha "$S/STORE.tsv")" "$K" "$(sha "$K")" "$C" "$(sha "$C")" "$PLACES" "$MEAN" "$(sha "$MEAN")" "$OUT/read" > "$OUT/read.log" 2>&1
  echo "# read: exit $? $(date -u +%H:%M:%S)"
)
grep -h "^STORE_PARITY" "$OUT/parity.log"
grep -q "^STORE_PARITY_DONE .* EQUAL$" "$OUT/parity.log" || status=1
if [ -n "$PARITY_LAP_LOG" ]; then
  python3 -I "$ROOT/tools/reproduction.py" "$OUT/parity.log" "$PARITY_LAP_LOG" 3 --no-save || status=1
else
  echo "GATE_PARITY_SECTIONS unread: no lap trained from the parity's state (the 24 sections below are the reproduction)"
fi
python3 -I "$ROOT/tools/reproduction.py" "$OUT/repro.log" "$LAP_LOG" 24 --no-save || status=1
if cmp "$OUT/read/cavity.tsv" "$READ_OUT/cavity.tsv"; then echo "GATE_READ cavity.tsv EQUAL"; else echo "GATE_READ cavity.tsv DIFFERS"; status=1; fi
grep -h "^MEASURE" "$OUT"/*.log
echo "GATE_ENGINE $([ $status -eq 0 ] && echo EQUAL || echo DIFFERS)"
exit $status
