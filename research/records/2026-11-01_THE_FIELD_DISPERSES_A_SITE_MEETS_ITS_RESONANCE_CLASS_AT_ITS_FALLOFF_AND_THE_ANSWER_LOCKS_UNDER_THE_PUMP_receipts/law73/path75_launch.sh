#!/bin/bash
# The boundary comparison follows the writer's path (§16.47, the unified-theory reading of November 5, 10:51): beside each
# training problem's region, one state of the writer's own reading order run on the truth (a keyed order of the extent's
# places, fresh each lap; its first k places resolved from the truth, every place past the lowest resolved void resolved
# as the void; k drawn so every octave of reads is met alike, k = 0 the opening), every open place compared at its
# boundary at weight one. First the sampled parity (it stops unless every read is equal), then a 150 s cost read that sets
# the lap bound, then trained from boundary73's segment 2's last state (where the opening already stands at its law), so the
# only change is the comparison along the writer's path, boundary73's own following segments its control at equal laps
# (the unified-theory reading of 10:53); five segments of 45 card-minutes on the state's own step, each followed by the
# opening read and the length reading's write of 32 held problems (length-field: the writer draw for draw, with its
# expected length at every read). The two chains share the card step by step under the lock.
# Prediction, fixed before launch (that reading), at each segment's last state: the mean drift of the expected length from
# read 0 to the written length under +20 places a problem; written places within a quarter of held; under 20 of 32 written
# longer; the opening's B at most 80; context and foil within boundary73's at equal laps from that state. Rule: drift under +20 and the
# write within a quarter, the law stands; drift under +20 but the write outside, the opening's own law (L at read 0) is the
# error left; drift over +20, the writer's own letters move its end where the truth's do not, and its own draws are the
# subject.
# Projection: parity, measured on boundary73's (its three training sections 51 to 93 s on the host, the rest as the free
# clock's), about 470 s, deadline 600 s; the cost read 150 s (outer 240 s); a lap measured there, the segments 2,760 s outer;
# each opening read 3.6 s (deadline 300 s); each write 1,558 s measured (the writer's stop 2,400 s, outer 2,700 s). The
# whole: 600 + 240 + 5 x (2,760 + 300 + 2,700) = 29,640 s at most of its own card time; expected about 6 h 30 min, interleaved
# with boundary73's segments 3 to 5 (about 3 h 30 min more). Detached (setsid). RTX 4080
# SUPER under .local/gpu.lock, 24 host threads; the lock is waited on up to 7,200 s, the other chains' projected steps
# between this chain's (a segment of 2,760 s and a 32-problem write of 1,558 s, with the readings between).
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-path75; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
A=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
CODEC=$R/2026-11-04-lane45/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
lock
# The sampled parity ran to its 600 s deadline (launch_parity.out): sections 1 and 2 read with their path states (resolved
# places inside the boundary ports), every face, covector entry, learner, near field, clock, row, share and current equal;
# section 3, the withheld section and the write were not reached (the path states' definite sources took the host's
# sections to 132 and 160 s). Not relaunched with a larger deadline: the reads the law changes are read and equal.
echo "# path75 binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
FROM=$(ls -t $R/2026-11-05-boundary73/seg2/STATE.* | grep -v stopped | head -1)
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
echo "# path75 from $(sha $FROM) $(date -u +%H:%M:%S)"
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
  python3 -I $O/opening.py $O/seg${seg}_opening $O/seg${seg}_write | grep -E '^written|^correlation'
  python3 -I $O/length.py $O/seg${seg}_write | sed -n '1,/^RULE/p'
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/seg${seg}_write/SAMPLE.tsv
  python3 -I $A/law56/written_restatements.py $O/seg${seg}_write/SAMPLE.tsv
  echo "SEGMENT $seg done $(date -u +%H:%M:%S)"
  FROM=$S
done
echo "MAIN exit $(date -u +%H:%M:%S)"
