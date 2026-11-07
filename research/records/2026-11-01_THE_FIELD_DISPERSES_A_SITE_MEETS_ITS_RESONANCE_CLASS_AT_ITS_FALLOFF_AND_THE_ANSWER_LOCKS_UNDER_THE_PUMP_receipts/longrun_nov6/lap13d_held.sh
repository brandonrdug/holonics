#!/bin/bash
# The held enumerated read of lap 13's STATE.stopped (stopped at its deadline after 781 of 1,543 sections): contrast-field
# with LAPS 0. Card under .local/gpu.lock; outer deadline 120 s.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap13d; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$O/lap/STATE.stopped
exec 9>$ROOT/.local/gpu.lock; flock -w 300 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
D=$O/held; rm -rf $D
timeout 120 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 0 64 3600000 60000 $D > $D.log 2>&1
echo "rc $?"
python3 -I $O/enumerated.py $D/ENUMERATED.tsv
python3 -I $O/singular.py $D/ENUMERATED.tsv $F84/dev/CODEC -1 | head -2
