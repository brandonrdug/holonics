#!/bin/bash
# The step's size, read three ways, then the main line (§16.41). Takes over from main49 once its two rate arms (30 card-minutes
# each from run48's alone state at rate 11 and 10) end: main49 is stopped before its main line, and this chain reads a third arm
# from the same state, the step's size following each section's own parabola (FIELD_STEP_PARABOLA: the first-order change
# from the covector, a; the change read at the full step, a + b; one octave a section toward μ* = −a/2b), 30 card-minutes. The
# main line then continues from the arm with the lowest mean of its last three joint reads, in three segments of 45
# card-minutes with a write after each, under that arm's law. Projection: the arm 30 minutes (outer 1,860 s); the segments as
# main49's (laps 195 to 219 s, bound 260 s; writes STOP_MS 700,000, outer 720 s), 2 h 35 min; the whole under 3 h 10 min.
# Detached (setsid). RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=<checkout>; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-main50; BIN=$O/field_pass; P=$R/2026-11-04-main49
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
timeout 7200 bash -c "until grep -q 'RATE last3' $P/launch.out 2>/dev/null; do sleep 5; done"
kill -TERM -$(cat $P/launch.pid) 2>/dev/null; pkill -TERM -f "$P/field_pass" 2>/dev/null; sleep 3
echo "# main49 stopped after its arms $(date -u +%H:%M:%S): $(grep 'RATE last3' $P/launch.out)"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
train() { # NAME FROM STOP_MS OUTER ENV...
  local name=$1 from=$2 stop=$3 outer=$4; shift 4
  exec 9>$ROOT/.local/gpu.lock
  flock -w 3600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
  echo "# $name from $(sha $from) started $(date -u +%H:%M:%S) $*"
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 "$@" $M $name timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 260000 260000 $stop $O/$name $from $(sha $from) > $O/$name.log 2>&1
  grep -E '^FIELD_(STEP_PARABOLA|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-200
  grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+).*own_nats_a_place=([0-9.]+).*information_nats_a_place=([0-9.]+).*/\1 \2 \3/' | tr '\n' ';'; echo
  grep -E '^FIELD_SECTION' $O/$name.log | sed -E 's/.*rate=([0-9]+).*/\1/' | uniq -c | tr '\n' ' ' | cut -c1-400; echo
  exec 9>&-
}
last3() { grep -E '^FIELD_JOINT_NATS' $1 | tail -3 | sed -E 's/.*own_nats_a_place=([0-9.]+).*/\1/' | awk '{s+=$1} END {printf "%.6f", s/NR}'; }
train parabola $R/2026-11-04-run48/alone/STATE.11 1800000 1860 FIELD_STEP_PARABOLA=1
A=$(last3 $P/rate11.log); B=$(last3 $P/rate10.log); C=$(last3 $O/parabola.log); echo "STEP last3 rate11=$A rate10=$B parabola=$C"
WIN=$P/rate11; LAW=FIELD_NONE=1; BEST=$A
awk -v a=$BEST -v b=$B 'BEGIN {exit !(b < a)}' && { WIN=$P/rate10; BEST=$B; }
awk -v a=$BEST -v c=$C 'BEGIN {exit !(c < a)}' && { WIN=$O/parabola; LAW=FIELD_STEP_PARABOLA=1; BEST=$C; }
FROM=$(ls -t $WIN/STATE.* | head -1); echo "STEP continuing $(basename $WIN) from $(basename $FROM) under $LAW"
for seg in 1 2 3; do
  train seg$seg $FROM 2700000 2760 $LAW
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
