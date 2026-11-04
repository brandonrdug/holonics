#!/bin/bash
# Lanes' first reading (§16.40's acceptance, fixed in §16.39 before the build): run41's alone state (STATE.11: D 256, H 4,
# f 256, rate 11; joint code 1.208 nats a place, the question 0.322; its head line rewritten to hnn-field-v13 with one lane,
# its body byte-equal) continued 45 card-minutes grown by one fresh lane to D 512 (FIELD_LANE_FIRST, its moments opened on
# their families' statistics), and 45 card-minutes alone, both under every law of the day, growth held so each stands at its
# width. Acceptance: the laned arm's joint code at least 0.035 nats a place below the alone arm's after the same wall time,
# and its volume (the expansion read's participation ratio at the last tick) at least 32; the written answers shown whole.
# Projection: the laned field's sections 0.73 s median, 0.81 s mean (lane45's probe, 212 sections), a lap 333 s and 370 s with
# its reads, about 7 laps in 2,700 s, lap bound 400 s; the alone arm's laps 186 to 208 s (run41), bound 260 s; STOP_MS
# 2,700,000, outer 2,760 s each. The writes (three refinement passes on 6 held problems): run41's alone write 365 s at D 256,
# the laned at most 1.7 times, 620 s; STOP_MS 700,000, outer 720 s, for both. Then the expansion read of both last states
# (seconds each, outer 300 s). The whole under 115 minutes. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-run46; BIN=$O/field_pass
FROM=$R/2026-11-04-lane45/FROM.v13; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) from $(sha $FROM) started $(date -u +%H:%M:%S)"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
arm() { # NAME LAPBOUND ENV
  local name=$1 bound=$2; shift 2
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 "$@" $M $name timeout 2760 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $bound $bound 2700000 $O/$name $FROM $(sha $FROM) > $O/$name.log 2>&1
  grep -E '^FIELD_(LANE|JOINT_NATS|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/$name.log | cut -c1-240
  local S=$(ls -t $O/$name/STATE.* 2>/dev/null | head -1)
  [ -n "$S" ] || { echo "$name no state"; return; }
  cp $CODEC $O/$name/CODEC 2>/dev/null
  $M ${name}_write timeout 720 $BIN train complete-language sample-field $S $(sha $S) $O/$name/CODEC $(sha $O/$name/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 3 700000 $O/${name}_write > $O/${name}_write.log 2>&1
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/${name}_write.log
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/${name}_write/SAMPLE.tsv
  echo "== $name expansion"
  timeout 300 $BIN train complete-language expansion-field "$S" $(sha "$S") $O/$name/CODEC $(sha $O/$name/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 8 2>&1 | grep -E '^FIELD_EXPANSION|rror|panic'
  echo "ARM $name done $(date -u +%H:%M:%S)"
}
arm laned 400000 FIELD_LANE_FIRST=1
arm alone 260000 FIELD_NONE=1
echo "FIELD_RUN exit $(date -u +%H:%M:%S)"
