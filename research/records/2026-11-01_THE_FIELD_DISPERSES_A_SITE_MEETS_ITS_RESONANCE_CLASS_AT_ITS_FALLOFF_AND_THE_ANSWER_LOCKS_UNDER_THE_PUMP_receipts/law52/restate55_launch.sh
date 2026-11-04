#!/bin/bash
# The restated results' ends across the clock's gaps (§16.42): restate-field on main52 seg1's last state (STATE.10) over the
# 128 held problems in five writer states; the two new ones open the `>>` between the result and its restatement, and every
# answer site but the result's, to read whether a blank site between a source and its receiver moves the offset the turned
# heads meet it at. Projection: restate54 read 3,537 reads in 36.1 s (10.2 ms a read); 393 restatements times 15 reads is
# 5,895 reads, 60 s; deadline 180 s. RTX 4080 SUPER under .local/gpu.lock (idle), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-04-restate55; BIN=$O/field_pass; S=$W/.local/run/2026-11-04-main52/seg1
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "RESTATE LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/read
$M read timeout 180 $BIN train complete-language restate-field $S/STATE.10 $(sha $S/STATE.10) $S/CODEC $(sha $S/CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 $O/read > $O/read.log 2>&1
grep -E '^FIELD_RESTATE|^FIELD_CARD |MEASURE|rror|panic' $O/read.log | cut -c1-260
echo "RESTATE exit $(date -u +%H:%M:%S)"
