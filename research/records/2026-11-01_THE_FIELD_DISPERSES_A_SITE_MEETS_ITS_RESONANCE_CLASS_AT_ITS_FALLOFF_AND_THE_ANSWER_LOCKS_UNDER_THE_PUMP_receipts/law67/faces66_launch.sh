#!/bin/bash
# Every face a clock reads is compared (§16.45, the unified-theory reading of November 5): the released face and each face a
# later tick's clock read off a blank, at the same open places with the same weight m/(K F), F the faces read, the released
# code reported as before; the exact return kept as this comparison's adjoint. Trained on the card from blank60's own opening
# state on its schedule (2^-12 under the transfer law), beside exact63 (the exact return alone) as its control. Five
# segments of 45 card-minutes, each followed by the acceptance read and a write of six held problems. Predicted (that
# reading): each clocked face's code near its entropy; (b) back to the old law's 5.04 to 5.25 or below; context and foil at
# or below blank60's; (a) still fails.
# Acceptance as blank60's: (a) with every answer place but C open, head 3's share at the exact offset above 0.45 and D's
# code under 3.60 bits; (b) the writer's first state under 5.08 bits a class; (c) context and foil reported. Projection from
# blank60: a lap 245 to 280 s, bound 300 s; each segment 2,760 s outer; each read 240 s outer; each write 720 s outer; the
# comparison of the clocked faces adds their fetches to each read (dev.out measures before launch). The
# whole: 5 x (2,760 + 240 + 720) = 18,600 s, 5 h 10 min. Detached (setsid). RTX 4080 SUPER under .local/gpu.lock, 24 host
# threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-05-faces66; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
CODEC=$R/2026-11-04-lane45/CODEC
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 3600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
read_at() { # NAME STATE
  lock
  rm -rf $O/$1
  $M $1 timeout 240 $BIN train complete-language restate-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 128 $O/$1 > $O/$1.log 2>&1
  exec 9>&-
  grep -E '^FIELD_RESTATE |^FIELD_RESTATE_FIRST|^MEASURE|rror|panic' $O/$1.log | cut -c1-200
  python3 -I $W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts/law60/acceptance.py $O/$1/RESTATEMENTS.tsv
}
train() { # NAME FROM STOP_MS OUTER ENV...
  local name=$1 from=$2 stop=$3 outer=$4; shift 4
  lock
  echo "# $name from $(sha $from) started $(date -u +%H:%M:%S) $*"
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 "$@" $M $name timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 $stop $O/$name $from $(sha $from) > $O/$name.log 2>&1
  exec 9>&-
  grep -E '^FIELD_(RATE|STEP_TRANSFER|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-200
  grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+).*own_nats_a_place=([0-9.]+).*information_nats_a_place=([0-9.]+).*/\1 \2 \3/' | tr '\n' ';'; echo
  grep -E '^FIELD_HELD' $O/$name.log | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
  grep -E '^FIELD_STEP_PRICE' $O/$name.log | sed -E 's/.*lap=([0-9]+).*least_milli=(-?[0-9]+) octave=(-?[0-9]+) rate=([0-9]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
}
FROM=$R/2026-11-04-main52/seg3/STATE.10
echo "# faces66 binary $(sha $BIN) from $(sha $FROM) $(date -u +%H:%M:%S)"
for seg in 1 2 3 4 5; do
  if [ $seg = 1 ]; then train seg$seg $FROM 2700000 2760 FIELD_RATE_BITS=12; else train seg$seg $FROM 2700000 2760; fi
  S=$(ls -t $O/seg$seg/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "segment $seg no state"; exit 1; }
  cp $CODEC $O/seg$seg/CODEC
  read_at seg${seg}_read $S
  lock
  $M seg${seg}_write timeout 720 $BIN train complete-language sample-field $S $(sha $S) $O/seg$seg/CODEC $(sha $O/seg$seg/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 3 700000 $O/seg${seg}_write > $O/seg${seg}_write.log 2>&1
  exec 9>&-
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/seg${seg}_write.log | cut -c1-200
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/seg${seg}_write/SAMPLE.tsv
  python3 -I $W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts/law56/written_restatements.py $O/seg${seg}_write/SAMPLE.tsv
  echo "SEGMENT $seg done $(date -u +%H:%M:%S)"
  FROM=$S
done
echo "MAIN exit $(date -u +%H:%M:%S)"
