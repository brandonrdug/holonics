#!/bin/bash
# The long run (Brandon, November 6 06:29 UTC: up to two hours to start, then free until 16:00 UTC if promising): code91's law
# (the fully masked opening the only path state, one keyed far place an octave on the one-rate clock; the near tail elsewhere)
# continued from code91's lap-4 state without the depth ring (its bracket gain in ring102 did not hold). Segments of two
# laps; after each the order reading (the opening's length code, beside its paired marginal), the opening reads, and two writes
# of the 32 held: the one-end writer (one uniform against the first read's void profile, the keyed sweeps given it) and the
# keyed sweeps given keyed100's lengths (the ring's brackets on a fixed room). Judged at two hours: held context against
# code91's 1.306, the paired length code, the writes' openings, fences and bracket closure (far brackets at least 0.8 of held's,
# near 0.9, unclosed under 0.1 for the ring). Projection: a lap about 25 card-minutes (code91's 792 ms a section); each
# segment's reads and writes about 6 minutes; six segments to about 13:00 UTC, each outer 3,453 s. No parity: every law here
# passed its own (code91's, ring102's). Detached; RTX 4080 SUPER under .local/gpu.lock, 24 host threads. It waits for ring102.
set -u
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-06-long106; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
CODEC=$F84/dev/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
echo "# long106 waits for ring102 $(date -u +%H:%M:%S)"
:
L=1546706; SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
FROM=$R/2026-11-06-code91/seg2/STATE.1
echo "# long106 from $(sha $FROM) $(date -u +%H:%M:%S)"
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
  FIELD_WRITER_LENGTHS=$R/2026-11-05-closing92/both_refine0/ENDS.tsv FIELD_WRITER_RUN_BITS=1 $M $1_keyed timeout 900 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/$1_keyed > $O/$1_keyed.log 2>&1
  exec 9>&-
  echo "== order $(grep -E '^FIELD_ORDER|^MEASURE|rror|panic' $O/$1_order.log | tr '\n' ' ' | cut -c1-400)"
  python3 -I $O/marginal.py $O/$1_order/ORDER.tsv $O/$1_HELD128/LENGTHS.tsv
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
for n in 2 3 4 5 6; do
  segment seg$n $(ls -t $O/seg$((n - 1))/STATE.* | grep -v stopped | head -1)
done
echo "MAIN exit $(date -u +%H:%M:%S)"
