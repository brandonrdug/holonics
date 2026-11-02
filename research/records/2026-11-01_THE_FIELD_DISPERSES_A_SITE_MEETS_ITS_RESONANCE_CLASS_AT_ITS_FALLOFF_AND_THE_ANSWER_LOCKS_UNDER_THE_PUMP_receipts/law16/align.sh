#!/usr/bin/env bash
# The founding's route to the clock and the anchor (§16), on the card: crib13's declaration at K = 3, the first
# section read and returned once, no deposit. Projection: one section's return (about 0.2 s on the card) and the
# host's readings of it (a few seconds); guard 120 s.
set -u
ROOT=$ROOT; W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
C=$W/.local/run/crib-closure; K=$W/.local/run/KEYS8; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD.txt $(sha $C/HELD.txt) $K $(sha $K)"
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo LOCK_BUSY; exit 75; }
echo "BIN=$(sha $BIN)"
python3 -I $W/.local/run/dispersing/measure.py align timeout 120 $BIN train complete-language align-field $T 32 5 8 2 32 3 16
