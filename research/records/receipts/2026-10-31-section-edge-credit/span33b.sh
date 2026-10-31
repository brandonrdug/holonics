#!/usr/bin/env bash
# The span release of span33.sh from lap 18's state (STATE.15), the state span33 meant to read
# (its sort chose lap 12's). Measured 375 s from lap 12's; span33's 1,600 s deadline kept.
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
S=$D/cont/STATE.15
K=$R/race/span/KEYS_SPAN
rm -rf $D/span18
echo "STATE=$(basename $S) $(sha256sum $S | cut -c1-64) at=$(date -u +%FT%TZ)"
TOWER_END_CLASS=30 timeout 1600 python3 -I $R/measure.py span-units-18 $R/bin/tower_pass-34a release complete-language release-span-tower-classes \
  $S $(sha256sum $S | cut -c1-64) $D/PROMPTS.units $(sha256sum $D/PROMPTS.units | cut -c1-64) \
  $K dc62532add8ad474bae69f088d8335b5d5314eb2ee5a92d9724e343d97d8703e 1024 2 320 $D/span18 > $D/span18.log 2>&1
echo "SPAN_END rc=$? $(grep -E 'CLASSES_SPAN|MEASURE|rror' $D/span18.log | tr '\n' ' ')"
