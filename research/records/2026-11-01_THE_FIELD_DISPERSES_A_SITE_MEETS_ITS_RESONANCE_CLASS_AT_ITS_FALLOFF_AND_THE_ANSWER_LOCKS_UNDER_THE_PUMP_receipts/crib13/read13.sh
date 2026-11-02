#!/usr/bin/env bash
# crib13's ten rested learners read for their held rows' concentration and temperatures (peaks-field), on the card,
# no deposit. Projection: about 10 states × 2 s; guard 300 s.
set -u
ROOT=$ROOT; W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
C=$W/.local/run/crib-closure; O=$W/.local/run/dispersing/crib13; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
S=()
for k in 0 1 2 3 4 5 6 7 8 9; do S+=("$O/train/STATE.$k" "$(sha $O/train/STATE.$k)"); done
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo LOCK_BUSY; exit 75; }
echo "BIN=$(sha $BIN) args=${#S[@]}"
python3 -I $W/.local/run/dispersing/measure.py peaks timeout 300 $BIN train complete-language peaks-field $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) $C/HELD.txt $(sha $C/HELD.txt) "${S[@]}"
