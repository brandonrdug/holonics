#!/bin/bash
# Regions end five places past their lowest void (part 2 of the unified-theory reading of November 5, 18:53, as amended at
# 19:32; FIELD_TAIL_NEAR): a training region's tail is the void and the five places past it, a path state past a resolved void
# ends five places past it, the withheld read's tail is cut alike. Trained from code84's lap-0 state for one segment of two
# laps, the same seed and keys, code84's segment 2 (parts 1 and 3 alone) its foil at equal laps. First its sampled parity on
# one section of this passage under the law.
# Prediction (that reading): held code on the context and opening reads stays no higher than code84's at equal laps (within
# its spread), and lap time falls again, about 1.6 times fewer sites than parts 1 and 3 alone. Rule: held code above that spread
# means the room's voids shaped what training learned about the end, and where the writer closes needs its own law.
# Projection: parity measured 400 s (deadline 900 s); the segment code84's, 2 x 679 s + 300 s (outer 1,717 s); its reads as
# code84's (300 s each, the drift 600 s, the write 3,300 s). RTX 4080 SUPER under .local/gpu.lock (waited on up to 7,200 s), 24
# host threads.
set -u
export FIELD_TAIL_NEAR=1
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-code85; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
CODEC=$F84/dev/CODEC
L=678865; SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
lock
echo "# code85 binary $(sha $BIN) parity lock taken $(date -u +%H:%M:%S)"
FIELD_PARITY_PACE=8 $M parity timeout 900 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 1 8 1 1 8 8 > $O/parity.log 2>&1
exec 9>&-
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY section|MEASURE|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
for f in faces_unequal=0 covector_unequal=0 learner_equal=true near_equal=true clocks_equal=true rows_equal=true shares_equal=true currents_equal=true; do
  grep -E 'FIELD_PARITY section' $O/parity.log | grep -qv "$f" && { echo "PARITY FAILED on $f: the chain stops"; exit 1; }
done
FROM=$F84/seg1/STATE.0
lock
echo "# seg2 from $(sha $FROM) started $(date -u +%H:%M:%S)"
rm -rf $O/seg2
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M seg2 timeout $OUTER $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $L $L $SEG $O/seg2 $FROM $(sha $FROM) > $O/seg2.log 2>&1
exec 9>&-
grep -E '^FIELD_(LAPS_HELD|STOPPED)|^FIELD_LAP |^MEASURE|rror|panic' $O/seg2.log | sed -E 's/ sites=[0-9]+//' | cut -c1-200
S=$(ls -t $O/seg2/STATE.* 2>/dev/null | grep -v stopped | head -1)
[ -n "$S" ] || { echo "no state"; exit 1; }
lock
for set in HELD128 TRAIN; do
  rm -rf $O/opening_$set
  $M opening_$set timeout 300 $BIN train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/$set.txt $(sha $P/$set.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) 128 $O/opening_$set > $O/opening_$set.log 2>&1
done
rm -rf $O/drift
$M drift timeout 600 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 128 2062 0 540000 $O/drift 64 $KEY > $O/drift.log 2>&1
exec 9>&-
for set in HELD128 TRAIN; do echo "== $set"; python3 -I $O/opening.py $O/opening_$set | grep -vE '^problem|^[0-9]+\s'; done
python3 -I $O/drift64.py state=$O/drift
echo "== against code84 at equal laps (FIELD_HELD: lap answer context foil; FIELD_UNSEEN; section ms)"
for run in $F84/seg2.log $O/seg2.log; do
  echo "$(basename $(dirname $run))/$(basename $run): $(grep -E '^FIELD_HELD' $run | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.-]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' ') | unseen $(grep -E '^FIELD_UNSEEN' $run | sed -E 's/.*lap=(-?[0-9]+).*code=([0-9.]+).*/\1:\2/' | tr '\n' ' ') | sections mean ms $(grep -E '^FIELD_SECTION' $run | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1} END {printf "%.0f over %d", s/n, n}')"
done
echo "CODE85 exit $(date -u +%H:%M:%S)"
