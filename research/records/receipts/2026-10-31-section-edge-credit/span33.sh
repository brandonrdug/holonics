#!/usr/bin/env bash
# §31's span release on §33's unit learner after its continuation (the latest state), agree 2, 320
# candidates, six prompts to 1,024 units; the end letter the record separator's unit 30. Projection
# from §31's byte release (809 s for 6,144 bytes' worth of classes; a unit span carries the same eight
# bits of news) and its 1,600 s deadline, which this keeps.
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
S=$(ls $D/cont/STATE.* | sort -t. -k2 -n | tail -1)
K=$R/race/span/KEYS_SPAN
rm -rf $D/span
echo "STATE=$(basename $S) $(sha256sum $S | cut -c1-64) at=$(date -u +%FT%TZ)"
TOWER_END_CLASS=30 timeout 1600 python3 -I $R/measure.py span-units $R/bin/tower_pass-34a release complete-language release-span-tower-classes \
  $S $(sha256sum $S | cut -c1-64) $D/PROMPTS.units $(sha256sum $D/PROMPTS.units | cut -c1-64) \
  $K dc62532add8ad474bae69f088d8335b5d5314eb2ee5a92d9724e343d97d8703e 1024 2 320 $D/span > $D/span.log 2>&1
echo "SPAN_END rc=$? $(grep -E 'CLASSES_SPAN|MEASURE|rror' $D/span.log | tr '\n' ' ')"
