#!/bin/bash
# The card kept working while the next law is built (Brandon, November 4 12:24: "make sure not idle"). Detached (setsid), so it
# outlives a session. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
# 1. The GPU suite of the field's card realization (gate 3 for the lanes' kernels, alone on the card); outer 1,800 s.
# 2. The step's size: run48's alone arm (D 256, rate 2^(−11); joint code 1.127 nats a place, its laps halved 0 or 1 times, so
#    every step stands at full size) continued 30 card-minutes at rate 11 and at rate 10 (FIELD_RATE_BITS). Question: whether
#    the step's size bounds the fall, read on the mean of each arm's last three joint reads. Laps 195 to 219 s, bound 260 s;
#    STOP_MS 1,800,000, outer 1,860 s each.
# 3. The main line from the lower arm, in three segments of 45 card-minutes (bound 260 s, STOP_MS 2,700,000, outer 2,760 s),
#    each followed by its write (three refinement passes on 6 held problems; STOP_MS 700,000, outer 720 s) and its words.
# Projection: suite under 30 minutes, arms 62 minutes, segments 2 h 35 min; the whole under 3 h 40 min.
set -u
ROOT=<checkout>; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-main49; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
echo "# suite build $(date -u +%H:%M:%S)"
(cd $W && PATH=/opt/cuda/bin:$PATH timeout 1200 cargo test --release -p holonics-cuda --no-run > $O/suite_build.txt 2>&1); echo "SUITE build rc=$?"
(cd $W && exec 9>$ROOT/.local/gpu.lock && flock -w 3600 9 && PATH=/opt/cuda/bin:$PATH timeout 1800 cargo test --release -p holonics-cuda -- --include-ignored --test-threads=1 field > $O/suite.txt 2>&1); echo "SUITE rc=$? $(grep -E '^test result' $O/suite.txt | tr '\n' ' ')"
grep -E 'FAILED|panicked' $O/suite.txt | head -5
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
train() { # NAME FROM STOP_MS OUTER ENV...
  local name=$1 from=$2 stop=$3 outer=$4; shift 4
  exec 9>$ROOT/.local/gpu.lock
  flock -w 3600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
  echo "# $name from $(sha $from) started $(date -u +%H:%M:%S)"
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 "$@" $M $name timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 260000 260000 $stop $O/$name $from $(sha $from) > $O/$name.log 2>&1
  grep -E '^FIELD_(RATE|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-200
  grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+).*own_nats_a_place=([0-9.]+).*information_nats_a_place=([0-9.]+).*/\1 \2 \3/' | tr '\n' ';'; echo
  exec 9>&-
}
last3() { grep -E '^FIELD_JOINT_NATS' $O/$1.log | tail -3 | sed -E 's/.*own_nats_a_place=([0-9.]+).*/\1/' | awk '{s+=$1} END {printf "%.6f", s/NR}'; }
FROM=$R/2026-11-04-run48/alone/STATE.11
train rate11 $FROM 1800000 1860 FIELD_NONE=1
train rate10 $FROM 1800000 1860 FIELD_RATE_BITS=10
A=$(last3 rate11); B=$(last3 rate10); echo "RATE last3 rate11=$A rate10=$B"
WIN=rate11; awk -v a=$A -v b=$B 'BEGIN {exit !(b < a)}' && WIN=rate10
FROM=$(ls -t $O/$WIN/STATE.* | head -1); echo "RATE continuing $WIN from $(basename $FROM)"
for seg in 1 2 3; do
  train seg$seg $FROM 2700000 2760 FIELD_NONE=1
  S=$(ls -t $O/seg$seg/STATE.* 2>/dev/null | head -1)
  [ -n "$S" ] || { echo "segment $seg no state"; exit 1; }
  cp $R/2026-11-04-lane45/CODEC $O/seg$seg/CODEC
  exec 9>$ROOT/.local/gpu.lock; flock -w 3600 9
  $M seg${seg}_write timeout 720 $BIN train complete-language sample-field $S $(sha $S) $O/seg$seg/CODEC $(sha $O/seg$seg/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 3 700000 $O/seg${seg}_write > $O/seg${seg}_write.log 2>&1
  exec 9>&-
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/seg${seg}_write.log | cut -c1-200
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/seg${seg}_write/SAMPLE.tsv
  echo "SEGMENT $seg done $(date -u +%H:%M:%S)"
  FROM=$S
done
echo "MAIN exit $(date -u +%H:%M:%S)"
