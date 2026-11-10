#!/bin/bash
# The card and the host's lanes as one surface (Brandon, November 7 19:22): the resumed lap's opening sections from STATE.0.680
# again, its energy reads split between the host's cores and the card (FIELD_HOST_LANES); each section must equal the
# card-only run's (resume.log) in every field but its time. About 40 sections: stop at 200 s. Card under .local/gpu.lock;
# host 20 threads.
set -u
export RAYON_NUM_THREADS=20 FIELD_HOST_LANES=1 FIELD_CONTRAST_BLOCK_PIN=1 FIELD_CONTRAST_BLOCK_PLACES=1 FIELD_CONTRAST_FROM_SECTION=680
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap12card; BIN=$O/field_lanes
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$O/lap/STATE.0.680
exec 9>$ROOT/.local/gpu.lock; flock -w 600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lanes check, lock $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/lanes; rm -rf $D
timeout 400 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 200000 200000 $D > $D.log 2>&1
echo "lanes rc $?"; grep -E '^FIELD_(LANES|STOPPED|CARD )|rror|panic' $D.log | cut -c1-300
python3 -I $O/lanes_compare.py $O/resume.log $D.log
