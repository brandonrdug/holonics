#!/bin/bash
# The restated results' ends in the writer's states (§16.42): restate-field on main52 seg1's last state (STATE.10, 1.012 nats
# a place, D 256, H 4, K 4) over the 128 held problems, each restatement's first place, last place and the place after it,
# alone open, with the restatement open, and with the result and its restatement open. Projection: copy53's development
# read took 984 ms for 84 reads (11.7 ms a read); about 450 restatements times 9 reads is about 4,050 reads, 47 s; deadline
# 180 s. RTX 4080 SUPER under .local/gpu.lock (taken after main52's segment 3 or its write), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-04-restate54; BIN=$O/field_pass; S=$W/.local/run/2026-11-04-main52/seg1
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "RESTATE LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/read
$M read timeout 180 $BIN train complete-language restate-field $S/STATE.10 $(sha $S/STATE.10) $S/CODEC $(sha $S/CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 $O/read > $O/read.log 2>&1
grep -E '^FIELD_RESTATE|^FIELD_CARD |MEASURE|rror|panic' $O/read.log | cut -c1-260
echo "RESTATE exit $(date -u +%H:%M:%S)"
