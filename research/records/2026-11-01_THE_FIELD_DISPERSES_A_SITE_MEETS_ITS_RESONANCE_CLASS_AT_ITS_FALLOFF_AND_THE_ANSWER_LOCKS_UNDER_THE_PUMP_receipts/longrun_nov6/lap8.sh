#!/bin/bash
# lap 8 (theory, November 7, 06:57): contrast-field's kernel from lap 5's STATE.0 at 16 states a section, moments 3 and 8,
# each family's length read from its own transfer (opening at 12 bits), the letters' temperature in the deposit; the
# enumerated read at 64 held places before and after. The development read (60 s): 18.94 ms a state -> 467 s a lap; log2 T
# fell from 14.57 to 10.50 in 169 sections; read_bias and lift_bias lengths ran past zero bits (their steps held at 2^0).
# Deadline 620 s (STOP_MS: 1.25x the projection plus the two enumerated reads; the lap stops after the section past it,
# writing STATE.stopped), outer timeout 720 s. Card: RTX 4080 SUPER under .local/gpu.lock, peak store 8.4 GB; host 8
# threads, 0.45 GB.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap8; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap4/lap5/STATE.0
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/lap; rm -rf $D
$M lap timeout 720 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 620000 620000 $D > $D.log 2>&1
grep -E '^FIELD_(KERNEL_ACCEPT|KERNEL_BLOCKS|KERNEL_TENTH|KERNEL_FAMILIES|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-1200
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv
python3 -I $O/tenths.py $D.log | head -13
[ -f $D/STATE.0 ] && echo "STATE.0 $(sha $D/STATE.0)"
echo "MAIN exit $(date -u +%H:%M:%S)"
