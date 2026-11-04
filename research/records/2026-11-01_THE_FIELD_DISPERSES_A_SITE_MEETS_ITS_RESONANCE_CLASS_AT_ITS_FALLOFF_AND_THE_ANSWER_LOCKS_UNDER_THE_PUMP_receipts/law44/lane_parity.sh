#!/bin/bash
# Lanes' card parity (§16.40): law27's sampled parity read (3 sections of GSM8K, 8 withheld problems, one write of 8 sweeps;
# D 32, H 4, n 8, still 2, f 32, K 2, paces drawn) on the founded field grown by one fresh lane (FIELD_PARITY_LANE=1: D 64 in
# two lanes of 32), every face, covector entry, learner, row, share and current read against the host; then the same read of
# the field alone, so the restructured chart reads one lane as before. Projection: the field alone 312 s (tower40's), the laned
# field at most twice; deadlines 800 s and 400 s. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-04-lane44; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "PARITY LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
echo "# binary sha $(sha $BIN) started $(date -u +%H:%M:%S)"
FIELD_PARITY_LANE=1 FIELD_PARITY_PACE=8 $M laned timeout 800 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 3 8 1 1 8 8 > $O/laned.log 2>&1
grep -E 'FIELD_PARITY_LANE|FIELD_PARITY_DONE|FIELD_PARITY_WRITE |FIELD_PARITY section|MEASURE|refused|rror|panic' $O/laned.log | cut -c1-260 | head -14
FIELD_PARITY_PACE=8 $M alone timeout 400 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 3 8 1 1 8 8 > $O/alone.log 2>&1
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY_WRITE |MEASURE|refused|rror|panic' $O/alone.log | cut -c1-260 | head -6
echo "PARITY exit $(date -u +%H:%M:%S)"
