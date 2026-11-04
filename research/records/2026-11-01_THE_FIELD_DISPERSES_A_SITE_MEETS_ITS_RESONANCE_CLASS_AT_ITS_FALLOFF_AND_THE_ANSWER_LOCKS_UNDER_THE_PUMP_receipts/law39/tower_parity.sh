#!/bin/bash
# The tower's card parity, second launch (the first stopped at the row read, which the driver refused for a tower and now
# reads): law27's sampled parity read (3 sections of GSM8K, 8 withheld problems, one write of 8 sweeps; D 32, H 4, n 8,
# still 2, f 32, K 2) on the founded field grown in scale (packets of 6 sites after its first tick, the prolongation drawn,
# FIELD_PARITY_SCALE=6). The field alone read equal through the restructured driver (launch.out). Projection: at most twice
# the field alone's 312 s; deadline 800 s. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-03-tower40; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "PARITY LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
echo "# binary sha $(sha $BIN)"
FIELD_PARITY_SCALE=6 FIELD_PARITY_PACE=8 $M tower timeout 800 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 3 8 1 1 8 8 > $O/tower2.log 2>&1
grep -E 'FIELD_PARITY_SCALE|FIELD_PARITY_DONE|FIELD_PARITY_WRITE |FIELD_PARITY section|MEASURE|refused|rror|panic' $O/tower2.log | cut -c1-260 | head -14
