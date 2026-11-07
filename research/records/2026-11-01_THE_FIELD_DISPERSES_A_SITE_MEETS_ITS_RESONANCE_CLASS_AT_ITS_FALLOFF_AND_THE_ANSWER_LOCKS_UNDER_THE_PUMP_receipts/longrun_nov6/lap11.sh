#!/bin/bash
# lap 11 again (theory, November 7, 08:13: the block size from the elasticity of the mean acceptance, two lengths a
# section k+ = ceil(k* 2^1/4) and k- = max(1, floor(k* 2^-1/4)) alternating, slope = ln(a+/a-)/ln(k+/k-), log2 k* +=
# (1 + slope)/4, opening at lap 10's last k* = 4), each problem's truth formed once, the family lengths carried, from lap
# 10's STATE.stopped. A one-minute development read first; the lap's deadline is its projection's upper end (1.25x plus the
# enumerated reads), run whole under Brandon's pre-authorization (November 7, 08:10). Card: RTX 4080 SUPER under
# .local/gpu.lock; host part 8 threads.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap11b; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap10/lap/STATE.stopped
ARGS="$S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64"
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/dev; rm -rf $D
FIELD_CONTRAST_BLOCK_PLACES=4 $M dev timeout 180 $BIN train complete-language contrast-field $ARGS 3600000 60000 $D > $D.log 2>&1
grep -E '^FIELD_(STOPPED|KERNEL_ACCEPT)|^MEASURE|rror|panic' $D.log | cut -c1-300
PROJ=$(grep '^FIELD_KERNEL lap' $D.log | python3 -I -c "
import sys
rows=[dict(kv.split('=') for kv in l.split()[1:]) for l in sys.stdin]
ms=sum(int(r['ms_section']) for r in rows)
print(int(24685*ms/(16*len(rows))))")
echo "# projection ${PROJ} ms; k* by section: $(grep '^FIELD_KERNEL lap' $D.log | grep -o 'k_star=[0-9]*' | cut -d= -f2 | tr '\n' ' ' | cut -c1-200)"
DEAD=$(( PROJ * 5 / 4 + 30000 ))
echo "# deadline ${DEAD} ms"
D=$O/lap; rm -rf $D
FIELD_CONTRAST_BLOCK_PLACES=4 $M lap timeout $(( DEAD / 1000 + 120 )) $BIN train complete-language contrast-field $ARGS $DEAD $DEAD $D > $D.log 2>&1
grep -E '^FIELD_(KERNEL_ACCEPT|KERNEL_BLOCKS|KERNEL_TENTH|KERNEL_FAMILIES|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-1200
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv
python3 -I $O/tenths.py $D.log | head -13
[ -f $D/STATE.0 ] && echo "STATE.0 $(sha $D/STATE.0)"
echo "MAIN exit $(date -u +%H:%M:%S)"
