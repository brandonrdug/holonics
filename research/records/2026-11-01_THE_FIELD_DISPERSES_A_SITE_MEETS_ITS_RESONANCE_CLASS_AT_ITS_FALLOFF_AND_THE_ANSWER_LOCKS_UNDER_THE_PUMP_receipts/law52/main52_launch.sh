#!/bin/bash
# The step priced where it generalizes (§16.41). Takes over from main51 at its first segment boundary after this chain's binary
# (the transfer reading, FIELD_STEP_PRICE a lap, and the FIELD_STEP_TRANSFER law) is in place: main51 is stopped as its next
# segment opens, and from the last state of the segment it finished three arms read 30 card-minutes each: the fixed rate 2^-11
# (the main line itself), the halved step 2^-12 (the doubled step rose 0.053 at once and fell three times faster, so the
# halved one should fall at once if the noise floor binds), and the transfer law. Every arm prints each step's price on the
# next section. The main line then continues from the arm with the lowest mean of its last three joint reads, under its law,
# in three segments of 45 card-minutes with a write after each.
# Projection: the arms 3 x 1,860 s outer; segments 3 x (2,760 + 720) s outer; the whole under 4 h 30 min.
# Detached (setsid). RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-main52; BIN=$O/field_pass; P=$R/2026-11-04-main51
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
timeout 3600 bash -c "until [ -x $BIN ]; do sleep 5; done" || { echo "MAIN no binary; main51 goes on"; exit 1; }
N0=$(grep -c '^SEGMENT .* done' $P/launch.out)
timeout 10800 bash -c "until [ \$(grep -c '^SEGMENT .* done' $P/launch.out) -gt $N0 ]; do sleep 5; done" || { echo "MAIN main51 reached no boundary"; exit 1; }
kill -TERM -$(cat $P/launch.pid) 2>/dev/null; pkill -TERM -f "$P/field_pass" 2>/dev/null; sleep 3
SEG=$(grep '^SEGMENT .* done' $P/launch.out | tail -1 | awk '{print $2}')
FROM=$(ls -t $P/seg$SEG/STATE.* | head -1)
echo "# main51 stopped after segment $SEG $(date -u +%H:%M:%S); binary $(sha $BIN); from $(basename $FROM)"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
train() { # NAME FROM STOP_MS OUTER ENV...
  local name=$1 from=$2 stop=$3 outer=$4; shift 4
  exec 9>$ROOT/.local/gpu.lock
  flock -w 3600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
  echo "# $name from $(sha $from) started $(date -u +%H:%M:%S) $*"
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 "$@" $M $name timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 260000 260000 $stop $O/$name $from $(sha $from) > $O/$name.log 2>&1
  grep -E '^FIELD_(RATE|STEP_TRANSFER|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-200
  grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+).*own_nats_a_place=([0-9.]+).*information_nats_a_place=([0-9.]+).*/\1 \2 \3/' | tr '\n' ';'; echo
  grep -E '^FIELD_STEP_PRICE' $O/$name.log | sed -E 's/.*lap=([0-9]+).*least_milli=(-?[0-9]+) octave=(-?[0-9]+) rate=([0-9]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
  exec 9>&-
}
last3() { grep -E '^FIELD_JOINT_NATS' $1 | tail -3 | sed -E 's/.*own_nats_a_place=([0-9.]+).*/\1/' | awk '{s+=$1} END {printf "%.6f", s/NR}'; }
train rate11 $FROM 1800000 1860 FIELD_NONE=1
train rate12 $FROM 1800000 1860 FIELD_RATE_BITS=12
train transfer $FROM 1800000 1860 FIELD_STEP_TRANSFER=1
A=$(last3 $O/rate11.log); B=$(last3 $O/rate12.log); C=$(last3 $O/transfer.log); echo "STEP last3 rate11=$A rate12=$B transfer=$C"
WIN=rate11; LAW=FIELD_NONE=1; BEST=$A
awk -v a=$BEST -v b=$B 'BEGIN {exit !(b < a)}' && { WIN=rate12; BEST=$B; }
awk -v a=$BEST -v c=$C 'BEGIN {exit !(c < a)}' && { WIN=transfer; LAW=FIELD_STEP_TRANSFER=1; BEST=$C; }
FROM=$(ls -t $O/$WIN/STATE.* | head -1); echo "STEP continuing $WIN from $(basename $FROM) under $LAW"
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
