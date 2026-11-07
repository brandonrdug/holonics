#!/bin/bash
# Lap 12 resumed (theory, November 7, 08:49 and 16:56: one place a block, each with its own coin): the first run was killed
# with the app's session near 18:14 UTC after 819 of 1,543 sections; its hourly saved state STATE.0.680 (held 2.501 nats a
# byte) resumes the lap at section 680 with the same keys (FIELD_CONTRAST_FROM_SECTION). Projection: the 863 sections left at
# 5.505 s a section (sections 166-819 of the killed run, no other jobs), 4,751 s; deadline 1.25x plus 30 s, 5,969 s. A saved
# state and a held read at least each hour. Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads.
set -u
export RAYON_NUM_THREADS=8 FIELD_CONTRAST_BLOCK_PIN=1 FIELD_CONTRAST_BLOCK_PLACES=1 FIELD_CONTRAST_FROM_SECTION=680
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap12card; BIN=$O/field_resume
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$O/lap/STATE.0.680
ARGS="$S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64"
exec 9>$ROOT/.local/gpu.lock; flock -w 300 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16), state $(sha $S | cut -c1-16)"
DEAD=5969000
D=$O/resume; rm -rf $D
$M lap timeout $(( DEAD / 1000 + 200 )) $BIN train complete-language contrast-field $ARGS $DEAD $DEAD $D > $D.log 2>&1
grep -E '^FIELD_(RESUMED|SAVED|KERNEL_ACCEPT|KERNEL_FAMILIES|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-500
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv
for f in $D/STATE.*; do echo "$f $(sha $f)"; done
echo "MAIN exit $(date -u +%H:%M:%S)"
