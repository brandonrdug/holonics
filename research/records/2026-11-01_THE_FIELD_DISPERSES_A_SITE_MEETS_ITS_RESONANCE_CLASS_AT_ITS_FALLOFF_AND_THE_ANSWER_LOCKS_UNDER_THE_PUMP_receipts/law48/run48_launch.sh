#!/bin/bash
# Lanes, read longer (§16.40): run46's two arms continued from their last states for another 45 card-minutes each, under the
# same law (FIELD_GROWTH_HELD; the laned state already carries its two lanes), so the comparison stands at 90 card-minutes from
# run41's alone state. Question: whether the laned field's steeper fall (laps 3 to 7: 0.050 nats a place against the alone
# arm's 0.025 over laps 3 to 7, the alone arm flat over its last five) persists past the alone arm's plateau. Projection: the
# laned laps 277 to 307 s (run46), bound 340 s; the alone 195 to 219 s, bound 260 s; STOP_MS 2,700,000, outer 2,760 s each;
# writes STOP_MS 700,000, outer 720 s (run46: 590 s and 340 s); then the half-tick expansion read of both last states (seconds).
# The whole under 110 minutes. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-run48; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) started $(date -u +%H:%M:%S)"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
arm() { # NAME FROM LAPBOUND
  local name=$1 from=$2 bound=$3
  rm -rf $O/$name
  echo "# $name from $(sha $from)"
  env FIELD_GROWTH_HELD=1 $M $name timeout 2760 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $bound $bound 2700000 $O/$name $from $(sha $from) > $O/$name.log 2>&1
  grep -E '^FIELD_(JOINT_NATS|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-240
  local S=$(ls -t $O/$name/STATE.* 2>/dev/null | head -1)
  [ -n "$S" ] || { echo "$name no state"; return; }
  cp $R/2026-11-04-lane45/CODEC $O/$name/CODEC
  $M ${name}_write timeout 720 $BIN train complete-language sample-field $S $(sha $S) $O/$name/CODEC $(sha $O/$name/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 3 700000 $O/${name}_write > $O/${name}_write.log 2>&1
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/${name}_write.log
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/${name}_write/SAMPLE.tsv
  echo "== $name expansion"
  timeout 300 $BIN train complete-language expansion-field "$S" $(sha "$S") $O/$name/CODEC $(sha $O/$name/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 8 2>&1 | grep -E '^FIELD_EXPANSION|rror|panic' | sed -E 's/ regions=8//; s/ delta=[0-9]+//'
  echo "ARM $name done $(date -u +%H:%M:%S)"
}
arm laned $R/2026-11-04-run46/laned/STATE.7 340000
arm alone $R/2026-11-04-run46/alone/STATE.11 260000
echo "FIELD_RUN exit $(date -u +%H:%M:%S)"
