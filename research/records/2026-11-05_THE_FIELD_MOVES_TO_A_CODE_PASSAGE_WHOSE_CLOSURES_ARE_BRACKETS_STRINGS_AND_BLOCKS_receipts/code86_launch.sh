#!/bin/bash
# The code passage on code85's laws (regions end five places past their lowest void, which stood against code84 at equal
# laps: held context 2.124 against 2.181 at lap 1, sections 166 ms against 382), continued from code85's fourth-lap state:
# a cost read under the law, then six segments of four laps, each followed by the opening reads, the drift read and a write of
# 32 held problems in runs with the code and closure readings. Projection: the cost read 150 s (outer 240 s); a lap about 255 s
# measured in code85, its bound set by the cost read; a segment four laps and five minutes; the write about 11 minutes
# measured (outer 3,300 s); about 3 h 30 min in all. Detached (setsid). RTX 4080 SUPER under .local/gpu.lock (waited on up
# to 7,200 s), 24 host threads.
set -u
export FIELD_TAIL_NEAR=1
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-code86; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
FROM=$R/2026-11-05-code85/seg2/STATE.3
rm -rf $O/dev2
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M dev2 timeout 240 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 150000 $O/dev2 $FROM $(sha $FROM) > $O/dev2.log 2>&1
exec 9>&-
grep -E '^FIELD_DECLARATION' $O/dev2.log | cut -c1-300
grep -E '^FIELD_SECTION' $O/dev2.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1; if ($1>m) m=$1} END {printf "dev sections %d mean_ms %.0f max_ms %d\n", n, s/n, m}'
grep -E '^MEASURE|rror|panic' $O/dev2.log
SECTIONS=$(grep -oE 'sections=[0-9]+' $O/dev2.log | head -1 | cut -d= -f2)
L=$(grep -E '^FIELD_SECTION' $O/dev2.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk -v n_s=$SECTIONS '{n++; s+=$1} END {printf "%d", 1.2*n_s*s/n}')
[ -n "$L" ] && [ "$L" -gt 0 ] || { echo "MAIN no lap bound: the chain stops"; exit 1; }
SEG=$((4 * L + 300000)); OUTER=$((SEG / 1000 + 60))
echo "# lap bound $L ms (1.2 times the cost read's lap over $SECTIONS sections); a segment $SEG ms, outer $OUTER s"
CODEC=$F84/dev/CODEC
read_at() { # NAME STATE
  lock
  for set in HELD128 TRAIN; do
    rm -rf $O/$1_$set
    $M $1_$set timeout 300 $BIN train complete-language opening-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $P/$set.txt $(sha $P/$set.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) 128 $O/$1_$set > $O/$1_$set.log 2>&1
  done
  rm -rf $O/$1_drift
  $M $1_drift timeout 600 $BIN train complete-language length-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 128 2062 0 540000 $O/$1_drift 64 $KEY > $O/$1_drift.log 2>&1
  exec 9>&-
  for set in HELD128 TRAIN; do
    echo "== $set"
    grep -E '^FIELD_OPENING|^MEASURE|rror|panic' $O/$1_$set.log | cut -c1-200
    python3 -I $O/opening.py $O/$1_$set | grep -vE '^problem|^[0-9]+\s'
  done
  echo "== drift $(grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$1_drift.log | tr '\n' ' ' | cut -c1-200)"
  python3 -I $O/drift64.py state=$O/$1_drift
}
train() { # NAME FROM STOP_MS OUTER [FROM_STATE]
  local name=$1 stop=$2 outer=$3 from=${4:-}
  lock
  echo "# $name from ${from:+$(sha $from)}${from:-the founding} started $(date -u +%H:%M:%S)"
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M $name timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $L $L $stop $O/$name ${from:+$from $(sha $from)} > $O/$name.log 2>&1
  exec 9>&-
  grep -E '^FIELD_(RATE|STEP_TRANSFER|LAPS_HELD|STOPPED)|^FIELD_LAP |^MEASURE|rror|panic' $O/$name.log | sed -E 's/ sites=[0-9]+//' | cut -c1-200
  grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+).*own_nats_a_place=([0-9.]+).*information_nats_a_place=([0-9.]+).*/\1 \2 \3/' | tr '\n' ';'; echo
  grep -E '^FIELD_HELD' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.-]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
}
for seg in 3 4 5 6 7 8; do
  train seg$seg $SEG $OUTER $FROM
  S=$(ls -t $O/seg$seg/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "segment $seg no state"; exit 1; }
  read_at seg${seg}_opening $S
  lock
  FIELD_WRITER_RUN_BITS=1 $M seg${seg}_write timeout 3300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 3 3000000 $O/seg${seg}_write > $O/seg${seg}_write.log 2>&1
  exec 9>&-
  grep -E '^FIELD_LENGTH|^MEASURE' $O/seg${seg}_write.log | cut -c1-200
  python3 -I $O/length.py $O/seg${seg}_write | sed -n '/^opening L/,/^RULE/p'
  python3 -I $O/code_reading.py $P/HELD128.txt $O/seg${seg}_write/SAMPLE.tsv
  python3 -I $O/code_closure.py $P/HELD128.txt $O/seg${seg}_write/SAMPLE.tsv
  python3 -I $R/2026-11-03-refine36/words.py $P/TRAIN.txt $O/seg${seg}_write/SAMPLE.tsv
  echo "SEGMENT $seg done $(date -u +%H:%M:%S)"
  FROM=$S
done
echo "MAIN exit $(date -u +%H:%M:%S)"
