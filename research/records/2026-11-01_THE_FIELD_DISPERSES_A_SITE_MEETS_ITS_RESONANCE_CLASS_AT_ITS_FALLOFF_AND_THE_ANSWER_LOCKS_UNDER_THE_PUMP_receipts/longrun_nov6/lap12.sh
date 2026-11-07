#!/bin/bash
# lap 12 again, on the card (theory, November 7, 08:49: one place a block, each with its own coin; deposit, T and family
# lengths as lap 10's), from the k = 4 lap's end (the best held state, 2.770 nats a byte); its A100 run was lost with its VM
# at 488 of 1,543 sections. A two-minute development read projects the lap; the deadline is 1.25x that plus the
# enumerated reads. Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads.
set -u
export RAYON_NUM_THREADS=8 FIELD_CONTRAST_BLOCK_PIN=1 FIELD_CONTRAST_BLOCK_PLACES=1
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap12card; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-pin4/lap/STATE.0
ARGS="$S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64"
exec 9>$ROOT/.local/gpu.lock; flock -w 300 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
# The development read (16:51, 33 sections, 141 s) projected the lap at 6,183,545 ms; the deadline is fixed from it. The
# first launch was stopped after 36 sections to add the hourly saved state (Brandon, November 6 17:11), then relaunched; the second after a few sections to add the held read at each saved state (theory, November 7 16:56).
PROJ=6183545
DEAD=$(( PROJ * 5 / 4 + 30000 ))
echo "# projection ${PROJ} ms, deadline ${DEAD} ms"
D=$O/lap; rm -rf $D
$M lap timeout $(( DEAD / 1000 + 200 )) $BIN train complete-language contrast-field $ARGS $DEAD $DEAD $D > $D.log 2>&1
grep -E '^FIELD_(SAVED|KERNEL_ACCEPT|KERNEL_BLOCKS|KERNEL_FAMILIES|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-500
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv && python3 -I $O/singular.py $D/ENUMERATED.tsv $F84/dev/CODEC 0 | head -2
python3 -I $O/tenths.py $D.log | head -13
for f in STATE.0 STATE.stopped; do [ -f $D/$f ] && echo "$f $(sha $D/$f)"; done
echo "MAIN exit $(date -u +%H:%M:%S)"
