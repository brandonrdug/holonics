#!/bin/bash
# §16.31's coherence read on the triple terrain: the base declaration, 10 laps (3.0 to 3.5 s a lap measured), each family's
# step coherence after every lap; lap bound 30 s, STOP_MS 120,000, outer 140 s. RTX 4080 SUPER under .local/gpu.lock.
set -u
ROOT=${ROOT:?the repository root}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy31; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 900 9 || { echo "LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $O/TRAIN.txt $(sha $O/TRAIN.txt) $O/HELD.txt $(sha $O/HELD.txt) $K $(sha $K)"
rm -rf $O/coh
FIELD_STEP_COHERENCE=1 timeout 140 $BIN train complete-language train-field $T 32 4 8 2 32 6 16 10 8 30000 30000 120000 $O/coh > $O/coh.log 2>&1
grep -E '^FIELD_STEP_COHERENCE' $O/coh.log
