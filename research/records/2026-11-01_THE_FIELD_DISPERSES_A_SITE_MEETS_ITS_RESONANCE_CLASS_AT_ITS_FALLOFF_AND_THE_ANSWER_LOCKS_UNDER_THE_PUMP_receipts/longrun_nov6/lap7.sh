#!/bin/bash
# lap 7 (theory, November 7, 06:26: more evidence a step): contrast-field's kernel on the card from lap 5's STATE.0 at
# sections of 256 states (the n of least card time a state in the development reads: 18.80, 17.36 and 14.57 ms a state at
# 16, 64 and 256), the rate 10, the moments counting states (2^0, 2^-4); the Newton terms read beside the step. Projection
# 24,685 x 14.57 ms = 360 s; deadline 500 s (STOP_MS, 1.3x plus the two enumerated reads), outer timeout 600 s. Card: RTX
# 4080 SUPER under .local/gpu.lock, peak store 8.4 GB; host part 8 threads, 0.9 GB.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap7; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap4/lap5/STATE.0
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/lap; rm -rf $D
$M lap timeout 600 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 256 1 64 500000 500000 $D > $D.log 2>&1
grep -E '^FIELD_(KERNEL_ACCEPT|KERNEL_BLOCKS|KERNEL_NEWTON|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-300
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv
python3 -I $O/tenths.py $D.log | head -13
[ -f $D/STATE.0 ] && echo "STATE.0 $(sha $D/STATE.0)"
echo "MAIN exit $(date -u +%H:%M:%S)"
