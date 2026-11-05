#!/bin/bash
# b1 (the unified-theory readings of November 5, 21:07 and 21:19): a silent stretch past a region's last arrival is one
# passage, every place there running the free clock at the first silent place's rate (Field::silent_stretch, the card's
# silent_stretch; its covectors return to that place), and the path states with no resolved void keep the whole room again,
# their far open places compared at the boundary (path_front_cut off). Trained from code84's lap-0 state at the same seed
# and keys, code85 (the near tail alone) its foil at equal laps. It takes the card when code86's segment 3 is done.
# Fixed before the read (21:19): hazard past held at least 3 times the hazard at or under it (code84's segment 2: 0.51);
# correlation with held above +0.3, written/held 0.7 to 1.4; the opening's void mass at held above 0.3, at +128 above 0.5;
# held context within 0.02 bits a byte of code85's (2.1237 at lap 1). Fail: hazard ratio under 1.5 after two laps; between
# 1.5 and 3, two more laps before deciding (segment 3 below, run only then).
# Projection: parity 400 s measured on the whole room (code84; deadline 900 s); the cost read 150 s (outer 240 s); it stops
# unless its section mean is at most 573 ms (1.5 times code84's 382, the reading's fraction rule: past it the keyed fraction
# is built); a segment two laps at the cost read's bound plus 300 s; the reads 300 s each, the drift 600 s, the write 3,300 s.
# About 1 h 30 min, 2 h 40 min with segment 3. Detached (setsid). RTX 4080 SUPER under .local/gpu.lock (waited on up to
# 7,200 s), 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-code87; BIN=$O/field_pass; F84=$R/2026-11-05-code84
F86=$R/2026-11-05-code86
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
CODEC=$F84/dev/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
kill_tree() { local p; for p in $(pgrep -P "$1"); do kill_tree "$p"; done; kill -TERM "$1" 2>/dev/null; }
# The cost read put the whole room at 616 ms a section (1.61 times code84's 382), past the 573 the first launch stopped at.
# agent-inferred: the reading's keyed fraction would train fewer path states to fit a lap to a clock, which the card law
# refuses (the design fixes the workload; a run that does not fit gets the card or a stated long run); 1.61 times is two laps
# of about 32 card-minutes, so b1 runs whole, as the reading itself preferred. The lap bound is the cost read's (1.2 times its
# mean over the 1,535 sections), set before this launch.
L=$(grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk -v n_s=1535 '{n++; s+=$1} END {printf "%d", 1.2*n_s*s/n}')
SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
FROM=$F84/seg1/STATE.0
echo "# code87 whole room: lap bound $L ms, a segment $SEG ms, outer $OUTER s $(date -u +%H:%M:%S)"
segment() { # NAME FROM
  lock
  echo "# $1 from $(sha $2) started $(date -u +%H:%M:%S)"
  rm -rf $O/$1
  FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M $1 timeout $OUTER $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $L $L $SEG $O/$1 $2 $(sha $2) > $O/$1.log 2>&1
  exec 9>&-
  grep -E '^FIELD_(LAPS_HELD|STOPPED)|^FIELD_LAP |^MEASURE|rror|panic' $O/$1.log | sed -E 's/ sites=[0-9]+//' | cut -c1-200
  grep -E '^FIELD_HELD' $O/$1.log | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.-]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
  grep -E '^FIELD_SECTION' $O/$1.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1} END {printf "sections mean ms %.0f over %d\n", s/n, n}'
  S=$(ls -t $O/$1/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "$1 no state"; exit 1; }
  lock
  for set in HELD128 TRAIN; do
    rm -rf $O/$1_$set
    $M $1_$set timeout 300 $BIN train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/$set.txt $(sha $P/$set.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) 128 $O/$1_$set > $O/$1_$set.log 2>&1
  done
  rm -rf $O/$1_drift
  $M $1_drift timeout 600 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 128 2062 0 540000 $O/$1_drift 64 $KEY > $O/$1_drift.log 2>&1
  FIELD_WRITER_RUN_BITS=1 $M $1_write timeout 3300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 3 3000000 $O/$1_write > $O/$1_write.log 2>&1
  exec 9>&-
  for set in HELD128 TRAIN; do
    echo "== $set"
    grep -E '^FIELD_OPENING|^MEASURE|rror|panic' $O/$1_$set.log | cut -c1-200
    python3 -I $O/opening.py $O/$1_$set | grep -vE '^problem|^[0-9]+\s'
  done
  echo "== drift $(grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$1_drift.log | tr '\n' ' ' | cut -c1-200)"
  python3 -I $O/drift64.py state=$O/$1_drift
  echo "== write"
  grep -E '^FIELD_LENGTH|^MEASURE' $O/$1_write.log | cut -c1-200
  python3 -I $O/endings.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv 2062
  python3 -I $O/code_reading.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv
  python3 -I $O/code_closure.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv
  python3 -I $R/2026-11-03-refine36/words.py $P/TRAIN.txt $O/$1_write/SAMPLE.tsv
  echo "SEGMENT $1 done $(date -u +%H:%M:%S)"
}
segment seg2 $FROM
RATIO=$(python3 -I $O/endings.py $P/HELD128.txt $O/seg2_write/SAMPLE.tsv 2062 | sed -nE 's/^HAZARD past\/under ([0-9.]+|nan).*/\1/p')
echo "# hazard ratio after two laps: $RATIO"
if python3 -c "import sys; r=float('$RATIO'); sys.exit(0 if 1.5 <= r < 3 else 1)"; then
  segment seg3 $(ls -t $O/seg2/STATE.* | grep -v stopped | head -1)
fi
echo "MAIN exit $(date -u +%H:%M:%S)"
