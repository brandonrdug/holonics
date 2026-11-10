#!/bin/bash
# A pinned comparison beside the A100's (k* = 8): from lap 10's STATE.stopped, k* held at 4 (lap 10's last read;
# FIELD_CONTRAST_BLOCK_PIN), each problem's truth formed once, the family lengths carried, the temperature learning. Lap 11's
# slope read ran k* to 4096 and raised the held code, so its law is not rerun. Projection about 2,300 s (lap 11's first
# development read at k* near 4: 90 ms a problem); deadline 2,900 s (STOP_MS), outer timeout 3,000 s; overnight runs
# pre-authorized (Brandon, November 7 08:10). Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-pin4; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap10/lap/STATE.stopped
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/lap; rm -rf $D
FIELD_CONTRAST_BLOCK_PIN=1 FIELD_CONTRAST_BLOCK_PLACES=4 $M lap timeout 3000 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 2900000 2900000 $D > $D.log 2>&1
grep -E '^FIELD_(KERNEL_ACCEPT|KERNEL_BLOCKS|KERNEL_FAMILIES|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-600
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv && python3 -I $O/singular.py $D/ENUMERATED.tsv $F84/dev/CODEC 0 | head -2
python3 -I $O/tenths.py $D.log | head -13
[ -f $D/STATE.0 ] && echo "STATE.0 $(sha $D/STATE.0)"
echo "MAIN exit $(date -u +%H:%M:%S)"
