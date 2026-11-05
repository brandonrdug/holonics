#!/bin/bash
# The code passage (Brandon, November 5 16:29: python-codes-25k in place of GSM8K): a fresh field founded on the same
# declaration (the byte alphabet changes, so no GSM8K state carries over), trained on the 24,685 training problems of
# tools/code_passage.py's records (question = the instruction and its input, answer = the code, every byte exact), with the
# laws that stand: the boundary port along the writer's path (its states the first k places of the writer's octave order,
# octave82's rule: the end's faces must meet the octave order's states before that writer is judged), the keyed passage of
# path problems, the octave writer and the one-place refine. First the sampled parity on one section of this passage (it stops unless every read is equal),
# then a 150 s cost read that sets the lap bound, then three segments of two laps each, each followed by the opening read
# on the 128 held problems and the first 128 training problems, the drift read (the 128 held, read 64, one key), and the
# length reading's write of 32 held problems with the code reading (fences, Python parse, identifiers) and the closure
# reading (the unified-theory reading of 16:36, fixed before the first write: written against held closure of brackets,
# strings and blocks by span, near under 6 and far 6 or more; prediction: far strings close under 0.5 of held and below far
# brackets; rule: any closure under 0.5 of held is the build's subject, by the rotor's ring law; if none, names next).
# Projection: parity unmeasured on this passage (GSM8K's sections 132 to 165 s on the host; here the regions reach about
# 3,900 places against 2,221), deadline 1,200 s; the cost read 150 s (outer 240 s); a lap measured there (projected about
# an hour: 1,543 sections against 413), each segment two laps plus five minutes, its outer timeout a minute past that; the
# opening reads 300 s each; the drift read 600 s; the write's stop 3,000 s, outer 3,300 s. A stated long run: about eight
# card-hours, its value the code passage's first learning and writes. Detached (setsid). RTX 4080 SUPER under
# .local/gpu.lock (waited on up to 7,200 s), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-code84; BIN=$O/field_pass
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"
KEY=7949c565cdd6d613
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
lock
echo "# code84 binary $(sha $BIN) parity lock taken $(date -u +%H:%M:%S)"
FIELD_PARITY_PACE=8 $M parity timeout 1200 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 1 8 1 1 8 8 > $O/parity.log 2>&1
exec 9>&-
grep -E 'FIELD_PASSAGE|FIELD_PARITY_DONE|FIELD_PARITY_WRITES|FIELD_PARITY section|MEASURE|refused|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
for f in faces_unequal=0 covector_unequal=0 learner_equal=true near_equal=true clocks_equal=true rows_equal=true shares_equal=true currents_equal=true; do
  grep -E 'FIELD_PARITY section' $O/parity.log | grep -qv "$f" && { echo "PARITY FAILED on $f: the chain stops"; exit 1; }
done
lock
echo "# code84 cost read, founded, lock taken $(date -u +%H:%M:%S)"
rm -rf $O/dev
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M dev timeout 240 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 150000 $O/dev > $O/dev.log 2>&1
exec 9>&-
grep -E '^FIELD_DECLARATION' $O/dev.log | cut -c1-300
grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1; if ($1>m) m=$1} END {printf "dev sections %d mean_ms %.0f max_ms %d\n", n, s/n, m}'
grep -E '^MEASURE|rror|panic' $O/dev.log
SECTIONS=$(grep -oE 'sections=[0-9]+' $O/dev.log | head -1 | cut -d= -f2)
L=$(grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk -v n_s=$SECTIONS '{n++; s+=$1} END {printf "%d", 1.2*n_s*s/n}')
[ -n "$L" ] && [ "$L" -gt 0 ] || { echo "MAIN no lap bound: the chain stops"; exit 1; }
SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
echo "# lap bound $L ms (1.2 times the cost read's lap over $SECTIONS sections); a segment $SEG ms, outer $OUTER s"
CODEC=$O/dev/CODEC
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
FROM=""
for seg in 1 2 3; do
  train seg$seg $SEG $OUTER $FROM
  S=$(ls -t $O/seg$seg/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "segment $seg no state"; exit 1; }
  read_at seg${seg}_opening $S
  lock
  $M seg${seg}_write timeout 3300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 3 3000000 $O/seg${seg}_write > $O/seg${seg}_write.log 2>&1
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
