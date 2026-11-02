#!/usr/bin/env bash
# crib14's projection read (§16.16): the lap's time at K = 3 (time-field), then two laps of the located run
# (FIELD_CLOCK=located: lap 0 on the founding clock, one boundary's location, lap 1) for the location's own time.
# Guards: time 60 s; the two laps at most 600 s (unmeasured at K = 3 and with the location: read, then projected).
set -u
ROOT=<root>
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
C=$W/.local/run/crib-closure
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/dispersing/crib14t; M="python3 -I $W/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
DECL="32 5 8 2 32 3 16"
rm -rf $O; mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 600 9 || { echo "LOCK_BUSY"; exit 75; }
START=$(date +%s); el() { echo $(( $(date +%s) - START )); }
T="$G/UNITS0 $(sha $G/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD.txt $(sha $C/HELD.txt) $K $(sha $K)"
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader)"
$M crib14t timeout 60 $BIN time complete-language time-field $T $DECL 16 8 4 64 > $O/time.log 2>&1
PA=$(num FIELD_TIME_LAP $O/time.log projection_ms)
echo "TIME at=$(el) $(grep -E 'FIELD_TIME_LAP|FIELD_TIME_RELEASES|MEASURE' $O/time.log | tr '\n' ' ') P_A=$PA"
[ -n "$PA" ] && [ $PA -gt 0 ] || { echo "NO_PROJECTION"; exit 1; }
FIELD_CLOCK=located $M crib14t timeout 600 $BIN train complete-language train-field $T $DECL 2 8 $((PA * 3)) $((PA * 6)) 590000 $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? at=$(el) $(grep -E 'FIELD_LAP |FIELD_CLOCK|FIELD_GROW|FIELD_STOPPED|FIELD_LAPS_HELD|FIELD_CARD |MEASURE|rror|refused' $O/train.log | tr '\n' ' ' | cut -c1-6000)"
