#!/bin/bash
# A lap's path problems are a keyed order of the whole passage (§16.47, the unified-theory reading of November 5, 12:31):
# each section's path states, compared at their boundary, are of problems cut from one keyed order of the whole passage,
# fresh each lap, in the sections' sizes (paths_of), so a step's boundary covector is of every length class at once; the
# masked regions stay with their sections. Trained as path75 with this one difference, from the same state (boundary73's
# segment 2's last), so its laps walk the same sections with the same draws and path75 is its control lap for lap.
# First the sampled parity on two sections (it stops unless every read is equal); then, once path75's segment 1 has been
# read, a 150 s cost read that sets the lap bound and five segments of 45 card-minutes, each followed by the opening read
# on the 128 held problems and the first 128 training problems (with the lean against the question-blind length law) and
# the length reading's write of 32 held problems.
# Prediction, fixed before launch (that reading): at every segment's last state the opening's expected length less held is
# within 10 places of the question-blind law's on the same problems (held +10.2, training -9.5), and the drift of L from
# read 0 to the written length is path75's at equal laps. Rule: the lean still swings by 30 places, the swing is not the
# sections', and the step is the subject.
# Projection: parity on two sections, measured on path75's (its two sections 132 and 160 s on the host, the withheld section
# and the write as the free clock's), about 360 s, deadline 600 s; the cost read 150 s (outer 240 s); a lap measured there,
# the segments 2,760 s outer; each opening read 3.6 s (deadline 300 s); each write 1,558 s measured (the writer's stop
# 2,400 s, outer 2,700 s). The whole: 600 + 240 + 5 x (2,760 + 2 x 300 + 2,700) = 31,140 s at most of its own card time;
# expected about 6 h, interleaved with path75's and boundary73's steps. Detached (setsid). RTX 4080 SUPER under
# .local/gpu.lock, 24 host threads; the lock is waited on up to 7,200 s (two other chains' steps, 2,760 + 2,700 s at most).
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-keyed79; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
A=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
CODEC=$R/2026-11-04-lane45/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
lock
echo "# keyed79 binary $(sha $BIN) parity lock taken $(date -u +%H:%M:%S)"
FIELD_PARITY_PACE=8 $M parity timeout 600 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 2 8 1 1 8 8 > $O/parity.log 2>&1
exec 9>&-
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY_WRITES|FIELD_PARITY section|MEASURE|refused|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
grep -E 'FIELD_PARITY section' $O/parity.log | grep -qvE 'near_equal=true rows_equal=true shares_equal=true currents_equal=true' && { echo "PARITY FAILED on a reading: the chain stops"; exit 1; }
# The training waits for path75's segment 1 to be read (the unified-theory reading of 12:31: the run after path75 reads).
timeout 14000 bash -c "until grep -qE '^SEGMENT 1 done|no state|LOCK_BUSY|chain stops' $R/2026-11-05-path75/launch.out; do sleep 30; done" || { echo "MAIN path75's segment 1 not read in 14,000 s: the chain stops"; exit 1; }
lock
FROM=$(ls -t $R/2026-11-05-boundary73/seg2/STATE.* | grep -v stopped | head -1)
echo "# keyed79 cost read from $(sha $FROM) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/dev
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M dev timeout 240 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 150000 $O/dev $FROM $(sha $FROM) > $O/dev.log 2>&1
exec 9>&-
grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1; if ($1>m) m=$1} END {printf "dev sections %d mean_ms %.0f max_ms %d lap_projection_s %.0f\n", n, s/n, m, 413*s/n/1000}'
grep -E '^MEASURE|rror|panic' $O/dev.log
L=$(grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1} END {printf "%d", 1.2*413*s/n}')
[ -n "$L" ] && [ "$L" -lt 1350000 ] || { echo "MAIN a lap of $L ms leaves under two laps a segment: the chain stops"; exit 1; }
echo "# lap bound $L ms (1.2 times the cost read's lap)"
read_at() { # NAME STATE
  lock
  for set in HELD128 TRAIN; do
    rm -rf $O/$1_$set
    $M $1_$set timeout 300 $BIN train complete-language opening-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $G/$set.txt $(sha $G/$set.txt) $G/TRAIN.txt $(sha $G/TRAIN.txt) 128 $O/$1_$set > $O/$1_$set.log 2>&1
  done
  exec 9>&-
  for set in HELD128 TRAIN; do
    echo "== $set"
    grep -E '^FIELD_OPENING|^MEASURE|rror|panic' $O/$1_$set.log | cut -c1-200
    python3 -I $O/opening.py $O/$1_$set | grep -vE '^problem|^[0-9]+\s'
    python3 -I $A/law73/lean.py $O/$1_$set
  done
}
train() { # NAME FROM STOP_MS OUTER ENV...
  local name=$1 from=$2 stop=$3 outer=$4; shift 4
  lock
  echo "# $name from $(sha $from) started $(date -u +%H:%M:%S) $*"
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 "$@" $M $name timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $L $L $stop $O/$name $from $(sha $from) > $O/$name.log 2>&1
  exec 9>&-
  grep -E '^FIELD_(RATE|STEP_TRANSFER|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-200
  grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+).*own_nats_a_place=([0-9.]+).*information_nats_a_place=([0-9.]+).*/\1 \2 \3/' | tr '\n' ';'; echo
  grep -E '^FIELD_HELD' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
  grep -E '^FIELD_STEP_PRICE' $O/$name.log | sed -E 's/.*lap=([0-9]+).*least_milli=(-?[0-9]+) octave=(-?[0-9]+) rate=([0-9]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
}
echo "# keyed79 from $(sha $FROM) $(date -u +%H:%M:%S)"
for seg in 1 2 3 4 5; do
  train seg$seg $FROM 2700000 2760
  S=$(ls -t $O/seg$seg/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "segment $seg no state"; exit 1; }
  cp $CODEC $O/seg$seg/CODEC
  read_at seg${seg}_opening $S
  lock
  $M seg${seg}_write timeout 2700 $BIN train complete-language length-field $S $(sha $S) $O/seg$seg/CODEC $(sha $O/seg$seg/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 3 2400000 $O/seg${seg}_write > $O/seg${seg}_write.log 2>&1
  exec 9>&-
  grep -E '^FIELD_LENGTH|^MEASURE' $O/seg${seg}_write.log | cut -c1-200
  python3 -I $O/opening.py $O/seg${seg}_opening_HELD128 $O/seg${seg}_write | grep -E '^written|^correlation'
  python3 -I $O/length.py $O/seg${seg}_write | sed -n '1,/^RULE/p'
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/seg${seg}_write/SAMPLE.tsv
  python3 -I $A/law56/written_restatements.py $O/seg${seg}_write/SAMPLE.tsv
  echo "SEGMENT $seg done $(date -u +%H:%M:%S)"
  FROM=$S
done
echo "MAIN exit $(date -u +%H:%M:%S)"
