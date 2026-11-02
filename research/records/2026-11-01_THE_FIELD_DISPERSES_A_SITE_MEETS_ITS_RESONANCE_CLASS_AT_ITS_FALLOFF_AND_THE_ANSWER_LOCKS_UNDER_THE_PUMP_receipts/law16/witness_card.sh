#!/usr/bin/env bash
# §16.10's three reads on the card: the completed witness on the crib codec and declaration at K = 3, every
# first-calculation operand digit of the held problems at its cut front, the faces' covector off the card.
# Projection: five reads of about 500 regions (the parity's withheld read of 512 regions took 0.5 s on the card);
# guard 300 s.
set -u
ROOT=$ROOT; W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
C=$W/.local/run/crib-closure; K=$W/.local/run/KEYS8; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD.txt $(sha $C/HELD.txt) $K $(sha $K)"
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo LOCK_BUSY; exit 75; }
echo "BIN=$(sha $BIN)"
python3 -I $W/.local/run/dispersing/measure.py witness timeout 300 $BIN train complete-language witness-field $T 3
