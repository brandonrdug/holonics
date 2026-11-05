#!/bin/bash
# The writer's drift to read 64 on all 128 held problems, the same keys on every state (§16.47, the unified-theory reading
# of November 5, 13:26): one draw a problem leaves about ±27 places of noise on a 32-problem write's mean excess, and read
# 64 carries 95 to 110% of the drift, so length-field is read on the 128 with READS 64 and no refine pass, keyed by the
# shared start state's hash (7949c565cdd6d613) on boundary73's segment 2 state (the start), boundary73's segment 3 state
# (the control) and path75's segment 1 state (the path law, matched lap for lap with the control); the drifts are paired
# problem by problem. Rule (that reading): path75's drift on this measure under +20 places, the path law removes the drift.
# Projection: a 32-problem write's read measured at 0.417 s (1,462 s over 3,509 reads), so 128 problems about 1.7 s a read and
# 65 reads about 110 s a state; the writer's stop 280 s, outer 300 s each, 900 s in all. RTX 4080 SUPER under
# .local/gpu.lock (one window between the chains' steps; the lock waited on up to 7,200 s), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-drift80; BIN=$O/field_pass; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
KEY=7949c565cdd6d613
START=$R/2026-11-05-boundary73/seg2/STATE.2; CONTROL=$R/2026-11-05-boundary73/seg3/STATE.2; PATH75=$R/2026-11-05-path75/seg1/STATE.2
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "DRIFT80 LOCK_BUSY"; exit 75; }
echo "# drift80 binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
for pair in start=$START control=$CONTROL path75=$PATH75; do
  name=${pair%%=*}; S=${pair#*=}
  rm -rf $O/$name
  $M $name timeout 300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 1229 0 280000 $O/$name 64 $KEY > $O/$name.log 2>&1
  echo "== $name $(sha $S | cut -c1-16) $(grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$name.log | tr '\n' ' ' | cut -c1-250)"
done
exec 9>&-
python3 -I $O/drift64.py start=$O/start control=$O/control path75=$O/path75
echo "DRIFT80 exit $(date -u +%H:%M:%S)"
