#!/bin/bash
# Where a section's time goes (theory, November 7 19:29): the card's own clock on every launch (FIELD_EVENTS), card alone,
# over about 20 of the resumed lap's sections from STATE.0.680: each kernel's card time, launches and share, and the card's
# kernels against the section's wall (the rest is the host and the transfers). Stop at 120 s. Card under .local/gpu.lock.
set -u
export RAYON_NUM_THREADS=8 FIELD_EVENTS=1 FIELD_CONTRAST_BLOCK_PIN=1 FIELD_CONTRAST_BLOCK_PLACES=1 FIELD_CONTRAST_FROM_SECTION=680
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap12card; BIN=$O/field_lanes
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$O/lap/STATE.0.680
exec 9>$ROOT/.local/gpu.lock; flock -w 600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# events read, lock $(date -u +%H:%M:%S)"
D=$O/events; rm -rf $D
timeout 300 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 120000 120000 $D > $D.log 2>&1
echo "events rc $?"; grep -E '^FIELD_(EVENT_SPLIT|STOPPED|CARD )|rror|panic' $D.log | cut -c1-300; grep '^FIELD_EVENT ' $D.log | head -25 | cut -c1-200
