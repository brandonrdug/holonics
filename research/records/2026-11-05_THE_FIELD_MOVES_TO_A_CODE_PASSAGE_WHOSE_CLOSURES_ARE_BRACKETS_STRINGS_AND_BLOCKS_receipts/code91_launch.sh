#!/bin/bash
# Length lives at one state (the unified-theory reading of November 6, 04:03): from code86's segment-3 state, the near tail at
# every content state, and the only path state the fully masked one (FIELD_PATH_OPENING with FIELD_PATH_FAR_KEYED): the whole
# room, one keyed place an octave of distance from the question compared at the boundary, weight one, on the one-rate clock.
# The writer: one end, one draw (FIELD_WRITER_ONE_END: one uniform against the first read's void profile), then the keyed
# sweeps given it, runs, no refine pass. Fixed: (1) held context within 0.05 of code86's 1.364 at laps 1 to 3; (2) the
# opening's length code at most 9.6 bits an answer (the marginal) by lap 3, at most 4 unread; (3) the one-end writer at lap 3:
# written/held 0.67 to 1.49, exact ```python at least 23, entropy 4.76 to 5.02 and the space 0.14 to 0.21, fences at least 22.
# Blind: all hold, (2) least sure. First the sampled parity, then a cost read, then two segments of two laps, each followed by
# the order reading (the length code), the opening reads and two writes: the one-end writer and the keyed sweeps alone.
# Projection: parity 336 s measured (deadline 900 s); the cost read 150 s (outer 240 s); a lap at its bound; the order read
# about 40 s (outer 900 s); the reads 300 s; each write 900 s. About 2 h. Detached (setsid). RTX 4080 SUPER under
# .local/gpu.lock (waited on up to 7,200 s), 24 host threads. It waits for code90.
set -u
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-06-code91; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
CODEC=$F84/dev/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
echo "# code91 waits for code90 $(date -u +%H:%M:%S)"
until grep -qE "^MAIN exit|chain stops|LOCK_BUSY" $R/2026-11-06-code90/launch.out; do sleep 20; done
lock
echo "# code91 binary $(sha $BIN) parity lock taken $(date -u +%H:%M:%S)"
FIELD_PARITY_PACE=8 $M parity timeout 900 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 1 8 1 1 8 8 > $O/parity.log 2>&1
exec 9>&-
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY section|MEASURE|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
for f in faces_unequal=0 covector_unequal=0 learner_equal=true near_equal=true clocks_equal=true rows_equal=true shares_equal=true currents_equal=true; do
  grep -E 'FIELD_PARITY section' $O/parity.log | grep -qv "$f" && { echo "PARITY FAILED on $f: the chain stops"; exit 1; }
done
FROM=$R/2026-11-05-code86/seg3/STATE.4
lock
echo "# cost read from $(sha $FROM) $(date -u +%H:%M:%S)"
rm -rf $O/dev
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M dev timeout 240 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 150000 $O/dev $FROM $(sha $FROM) > $O/dev.log 2>&1
exec 9>&-
grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1; if ($1>m) m=$1} END {printf "dev sections %d mean_ms %.0f max_ms %d\n", n, s/n, m}'
grep -E '^MEASURE|rror|panic' $O/dev.log
L=$(grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk -v n_s=1535 '{n++; s+=$1} END {printf "%d", 1.2*n_s*s/n}')
[ -n "$L" ] && [ "$L" -gt 0 ] || { echo "MAIN no lap bound: the chain stops"; exit 1; }
SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
echo "# lap bound $L ms; a segment $SEG ms, outer $OUTER s"
segment() { # NAME FROM
  lock
  echo "# $1 from $(sha $2) started $(date -u +%H:%M:%S)"
  rm -rf $O/$1
  FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M $1 timeout $OUTER $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $L $L $SEG $O/$1 $2 $(sha $2) > $O/$1.log 2>&1
  exec 9>&-
  grep -E '^FIELD_(LAPS_HELD|STOPPED)|^FIELD_LAP |^MEASURE|rror|panic' $O/$1.log | sed -E 's/ sites=[0-9]+//' | cut -c1-200
  grep -E '^FIELD_HELD' $O/$1.log | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.-]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
  grep -E '^FIELD_UNSEEN' $O/$1.log | sed -E 's/.*lap=(-?[0-9]+) code=([0-9.]+).*/\1:\2/' | tr '\n' ' '; echo
  grep -E '^FIELD_SECTION' $O/$1.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1} END {printf "sections mean ms %.0f over %d\n", s/n, n}'
  S=$(ls -t $O/$1/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "$1 no state"; exit 1; }
  lock
  rm -rf $O/$1_order
  $M $1_order timeout 900 $BIN train complete-language order-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 $O/$1_order > $O/$1_order.log 2>&1
  for set in HELD128 TRAIN; do
    rm -rf $O/$1_$set
    $M $1_$set timeout 300 $BIN train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/$set.txt $(sha $P/$set.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) 128 $O/$1_$set > $O/$1_$set.log 2>&1
  done
  rm -rf $O/$1_place $O/$1_keyed
  FIELD_WRITER_ONE_END=1 FIELD_WRITER_RUN_BITS=1 $M $1_place timeout 900 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/$1_place > $O/$1_place.log 2>&1
  FIELD_WRITER_RUN_BITS=1 $M $1_keyed timeout 900 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/$1_keyed > $O/$1_keyed.log 2>&1
  exec 9>&-
  echo "== order $(grep -E '^FIELD_ORDER|^MEASURE|rror|panic' $O/$1_order.log | tr '\n' ' ' | cut -c1-260)"
  for set in HELD128 TRAIN; do
    echo "== $set"
    python3 -I $O/opening.py $O/$1_$set | grep -vE '^problem|^[0-9]+\s'
  done
  for w in place keyed; do  # place: the one-end writer
    echo "== write $w"
    grep -E '^FIELD_LENGTH|^MEASURE' $O/$1_$w.log | cut -c1-200
    python3 -I $O/endings.py $P/HELD128.txt $O/$1_$w/SAMPLE.tsv 2062
    python3 -I $O/collapse.py $P/HELD128.txt $O/$1_$w/SAMPLE.tsv | head -1
    python3 -I $O/code_reading.py $P/HELD128.txt $O/$1_$w/SAMPLE.tsv | sed -n 2p
    python3 -I $O/code_closure.py $P/HELD128.txt $O/$1_$w/SAMPLE.tsv
  done
  echo "SEGMENT $1 done $(date -u +%H:%M:%S)"
}
segment seg1 $FROM
segment seg2 $(ls -t $O/seg1/STATE.* | grep -v stopped | head -1)
echo "MAIN exit $(date -u +%H:%M:%S)"
