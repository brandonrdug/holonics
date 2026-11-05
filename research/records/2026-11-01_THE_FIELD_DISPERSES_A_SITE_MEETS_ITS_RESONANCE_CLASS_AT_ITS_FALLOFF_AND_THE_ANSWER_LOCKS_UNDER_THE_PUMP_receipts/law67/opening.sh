#!/bin/bash
# The void's mass across the writer's opening (§16.46, the unified-theory reading of November 5, 07:16, its rule fixed
# before the read): opening-field on exact63 segment 5's last state over the 128 held problems, each the writer's own
# opening (the question resolved, the codec's whole extent open), then opening.py beside the 32-problem write. Projection: a
# region a read, 128 reads (reach-field read 384 in 8.4 s, but these regions are the whole room, 1,229 open places), under
# a minute; deadline 300 s. RTX 4080 SUPER under .local/gpu.lock (after the write), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-write71; BIN=$O/field_pass; S=$R/2026-11-05-exact63/seg5/STATE.8; CODEC=$R/2026-11-05-exact63/seg5/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "OPENING LOCK_BUSY"; exit 75; }
echo "# opening binary $(sha $BIN) state $(sha $S) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/opening
$M opening timeout 300 $BIN train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) $G/TRAIN.txt $(sha $G/TRAIN.txt) 128 $O/opening > $O/opening.log 2>&1
exec 9>&-
grep -E '^FIELD_OPENING|^MEASURE|rror|panic' $O/opening.log | cut -c1-250
python3 -I $O/opening.py $O/opening $O/write
echo "OPENING exit $(date -u +%H:%M:%S)"
