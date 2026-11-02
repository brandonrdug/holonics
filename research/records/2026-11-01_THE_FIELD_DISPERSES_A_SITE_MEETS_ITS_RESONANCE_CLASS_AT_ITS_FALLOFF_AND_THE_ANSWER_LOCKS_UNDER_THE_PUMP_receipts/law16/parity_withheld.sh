#!/usr/bin/env bash
# The paced field's card parity (§16): the founding learns 4 sections on host and card, read bit for bit (the
# pace family is plain at the founding and moves with the first deposit, so later sections read the paced law).
# Projection: unmeasured with paces; read for 3 minutes (host reference dominates), then projected.
set -u
ROOT=<root>; W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
C=$W/.local/run/crib-closure; K=$W/.local/run/KEYS8; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD.txt $(sha $C/HELD.txt) $K $(sha $K)"
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo LOCK_BUSY; exit 75; }
echo "BIN=$(sha $BIN) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) grow=$GROW"
python3 -I $W/.local/run/dispersing/measure.py parity_pace timeout ${GUARD:-180} $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 $SECTIONS 8 $GROW ${RELEASES:-2} 40 2>&1 | grep -vE '^FIELD_PARITY_RELEASE' | tail -12
