#!/bin/bash
# The drift bound at every later segment (§16.47, the unified-theory reading of November 5, 14:20, fixed before these reads):
# at each path75 segment from 2 and each keyed79 segment, once the chain has read and written it ("SEGMENT n done"), the
# writer's drift L(64) - L(0) on all 128 held problems, read 64, the shared key 7949c565cdd6d613 (as drift80), paired with
# the start's. Bound: between -20 and +20 places (below -20 the path law overcorrects and pushes the writer short).
# Projection: 150 s a state measured (drift80), outer 300 s each; nine states, 2,700 s at most of card time, each in its own
# window between the chains' steps. RTX 4080 SUPER under .local/gpu.lock (waited on up to 7,200 s), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-drift80; BIN=$O/field_pass; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
KEY=7949c565cdd6d613
pending="path75:2 path75:3 path75:4 path75:5 keyed79:1 keyed79:2 keyed79:3 keyed79:4 keyed79:5"
deadline=$(( $(date +%s) + 40000 ))
while [ -n "$pending" ] && [ $(date +%s) -lt $deadline ]; do
  left=""
  for item in $pending; do
    chain=${item%%:*}; n=${item#*:}; out=$R/2026-11-05-$chain/launch.out
    if grep -qE "chain stops|no state|LOCK_BUSY" $out; then echo "# $item: the chain stopped, not read"; continue; fi
    if ! grep -q "^SEGMENT $n done" $out; then left="$left $item"; continue; fi
    S=$(ls -t $R/2026-11-05-$chain/seg$n/STATE.* | grep -v stopped | head -1)
    name=${chain}_seg$n
    exec 9>$ROOT/.local/gpu.lock
    flock -w 7200 9 || { echo "FOLLOW LOCK_BUSY"; exit 75; }
    rm -rf $O/$name
    $M $name timeout 300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 1229 0 280000 $O/$name 64 $KEY > $O/$name.log 2>&1
    exec 9>&-
    echo "== $name $(basename $S) $(sha $S | cut -c1-16) $(date -u +%H:%M:%S) $(grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$name.log | tr '\n' ' ' | cut -c1-250)"
    python3 -I $O/drift64.py start=$O/start $name=$O/$name | sed -n '2,$p'
  done
  pending=$(echo $left)
  [ -n "$pending" ] && sleep 60
done
echo "FOLLOW exit $(date -u +%H:%M:%S) pending: ${pending:-none}"
