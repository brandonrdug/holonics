#!/bin/bash
# b2's far share on b1's whole room (the unified-theory reading of November 5, 23:26; FIELD_PATH_FAR_KEYED): a path state
# with no resolved void compares its front octave whole and one keyed place an octave past it at the boundary, weight one,
# the places between read on the one-rate clock and not compared (the port's heard); the near tail as built. From code84's
# lap-0 state at the same seed and keys, code85 its foil at equal laps. First the sampled parity under the law.
# Fixed before the run (23:26): (1) held context within 0.05 of code85's at laps 0 to 3 (2.404, 2.124, 1.914, 1.579);
# (2) by lap 2 (segment 1's reads, after laps 0 and 1) the opening's void mass above code86's flat 0.09 at held, and higher at
# held+128 than at held; (3) with both writer laws the correlation with held above +0.3 by lap 4 (segment 2's write). If (1)
# fails the far share was not the dilution, and b1's clock is next; (2) flat through lap 4: the end's share is too slow at
# content's rate; only (3) failing: read where the writes end against their own closing fence. None raises the far weight.
# It keeps b1's geometry, so it reads the far share alone; b2 proper also drops the places between.
# Projection: parity 336 s measured on the whole room (deadline 900 s); a lap b1's, its bound 1,134,290 ms (b1's cost read,
# the same regions); two segments of two laps (outer 2,629 s each); the reads 300 s each, the drift 600 s, each write 600 s.
# About 2 h 10 min. Detached (setsid). RTX 4080 SUPER under .local/gpu.lock (waited on up to 7,200 s), 24 host threads.
set -u
export FIELD_PATH_FAR_KEYED=1
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-code88; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
CODEC=$F84/dev/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
lock
echo "# code88 binary $(sha $BIN) parity lock taken $(date -u +%H:%M:%S)"
FIELD_PARITY_PACE=8 $M parity timeout 900 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 1 8 1 1 8 8 > $O/parity.log 2>&1
exec 9>&-
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY section|MEASURE|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
for f in faces_unequal=0 covector_unequal=0 learner_equal=true near_equal=true clocks_equal=true rows_equal=true shares_equal=true currents_equal=true; do
  grep -E 'FIELD_PARITY section' $O/parity.log | grep -qv "$f" && { echo "PARITY FAILED on $f: the chain stops"; exit 1; }
done
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
  lock
  rm -rf $O/$1_sweeps
  FIELD_WRITER_RUN_BITS=1 $M $1_sweeps timeout 600 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/$1_sweeps > $O/$1_sweeps.log 2>&1
  exec 9>&-
  echo "== the sweeps' write (runs, no refine pass)"
  grep -E '^FIELD_LENGTH|^MEASURE' $O/$1_sweeps.log | cut -c1-200
  python3 -I $O/endings.py $P/HELD128.txt $O/$1_sweeps/SAMPLE.tsv 2062
  python3 -I $O/collapse.py $P/HELD128.txt $O/$1_sweeps/SAMPLE.tsv
  python3 -I $O/code_reading.py $P/HELD128.txt $O/$1_sweeps/SAMPLE.tsv
  python3 -I $O/unwrote.py $O/$1_sweeps
  echo "== the refined write"
  python3 -I $O/collapse.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv | head -1
  echo "SEGMENT $1 done $(date -u +%H:%M:%S)"
}
L=1134290; SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
segment seg1 $F84/seg1/STATE.0
segment seg2 $(ls -t $O/seg1/STATE.* | grep -v stopped | head -1)
echo "MAIN exit $(date -u +%H:%M:%S)"
