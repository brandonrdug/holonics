#!/bin/bash
# The opening compared at its boundary (§16.47, the unified-theory reading of November 5, 08:09): beside each training
# problem's region, its writer's opening (the question resolved, the codec's whole extent open), each place compared at
# weight one with whether the answer has ended there (a letter place: -log2(1 - p_void), its covector the void against the
# letters by their own shares; a place past the end: the void). First the sampled parity (it stops unless every read is
# equal), then a 150 s cost read that sets the lap bound, then trained as exact63 with that one difference: from main52 seg3's
# last state at 2^-12 under the transfer law, exact63 its control at equal card time. Five segments of 45 card-minutes, each
# followed by the opening read (opening-field and opening.py) and a write of 32 held problems.
# Prediction, fixed before launch (that reading), at every segment's last state: B <= 80 places; void share at +128 >= 0.754
# and at +512 >= 0.988; void mass before the end <= 52; context and foil within exact63's spread; written places within 25%
# of held; under 20 of 32 written longer. Rule: B <= 80 with no overrun, the boundary was the cause and the law stands; B
# falls but the writing still overruns, the overrun is made after the opening (the next subject); B stays over 80, the
# question is not heard 500 places out at this reach (the reach is the subject).
# Projection: parity 306 s (deadline 400 s); the cost read 150 s (outer 240 s); a lap measured there, the segments 2,760 s
# outer; each opening read 3.6 s (deadline 300 s); each write 2,293 s measured (the writer's stop 2,400 s, outer 2,700 s).
# The whole: 400 + 240 + 5 x (2,760 + 300 + 2,700) = 29,440 s at most, 8 h 11 min; expected about 7 h 15 min. Detached
# (setsid). RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-boundary73; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
A=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
CODEC=$R/2026-11-04-lane45/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 3600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
lock
# The sampled parity ran to its copied 400 s deadline (launch_parity.out): sections 1 to 3 read with their openings, every
# face, covector entry, learner, near field, clock, row, share and current equal; the withheld section and the write, whose
# code the boundary does not touch (no region there declares a port), were not reached. Not relaunched with a larger
# deadline: the openings tripled its host sections (51 to 93 s against 16 to 22 s), and the reads the law changes are read.
echo "# boundary73 binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
FROM=$R/2026-11-04-main52/seg3/STATE.10
rm -rf $O/dev
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 FIELD_RATE_BITS=12 $M dev timeout 240 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 150000 $O/dev $FROM $(sha $FROM) > $O/dev.log 2>&1
exec 9>&-
grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1; if ($1>m) m=$1} END {printf "dev sections %d mean_ms %.0f max_ms %d lap_projection_s %.0f\n", n, s/n, m, 413*s/n/1000}'
grep -E '^MEASURE|rror|panic' $O/dev.log
L=$(grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1} END {printf "%d", 1.2*413*s/n}')
[ -n "$L" ] && [ "$L" -lt 1350000 ] || { echo "MAIN a lap of $L ms leaves under two laps a segment: the chain stops"; exit 1; }
echo "# lap bound $L ms (1.2 times the cost read's lap)"
read_at() { # NAME STATE
  lock
  rm -rf $O/$1
  $M $1 timeout 300 $BIN train complete-language opening-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) $G/TRAIN.txt $(sha $G/TRAIN.txt) 128 $O/$1 > $O/$1.log 2>&1
  exec 9>&-
  grep -E '^FIELD_OPENING|^MEASURE|rror|panic' $O/$1.log | cut -c1-200
  python3 -I $O/opening.py $O/$1 | grep -vE '^problem|^[0-9]+\s'
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
echo "# boundary73 from $(sha $FROM) $(date -u +%H:%M:%S)"
for seg in 1 2 3 4 5; do
  if [ $seg = 1 ]; then train seg$seg $FROM 2700000 2760 FIELD_RATE_BITS=12; else train seg$seg $FROM 2700000 2760; fi
  S=$(ls -t $O/seg$seg/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "segment $seg no state"; exit 1; }
  cp $CODEC $O/seg$seg/CODEC
  read_at seg${seg}_opening $S
  lock
  $M seg${seg}_write timeout 2700 $BIN train complete-language sample-field $S $(sha $S) $O/seg$seg/CODEC $(sha $O/seg$seg/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 3 2400000 $O/seg${seg}_write > $O/seg${seg}_write.log 2>&1
  exec 9>&-
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/seg${seg}_write.log | cut -c1-200
  python3 -I $O/opening.py $O/seg${seg}_opening $O/seg${seg}_write | grep -E '^written|^correlation'
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/seg${seg}_write/SAMPLE.tsv
  python3 -I $A/law56/written_restatements.py $O/seg${seg}_write/SAMPLE.tsv
  echo "SEGMENT $seg done $(date -u +%H:%M:%S)"
  FROM=$S
done
echo "MAIN exit $(date -u +%H:%M:%S)"
