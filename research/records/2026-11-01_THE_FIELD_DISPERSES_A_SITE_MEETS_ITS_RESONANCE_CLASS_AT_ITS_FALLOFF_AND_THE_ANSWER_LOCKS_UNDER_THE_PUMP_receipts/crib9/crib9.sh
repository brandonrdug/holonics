#!/usr/bin/env bash
# The crib probe under the dispersing field (record 2026-11-01_THE_FIELD_DISPERSES_…, §7): the crib terrain
# (seed 20261101, 4,096 training problems and 128 held, as §19's probe), reading 8's declaration, keys, section
# and rate (D 32, H 4, n 8, still 2, f 32, K 2, SECTION 16, RATE 8). Bar: at least 24 of 126 first calculations
# from the question, above its foil.
# The partition, fixed here before launch (each slot is its command's outer timeout; nothing raised or relaunched):
#   parity A 45 s, parity B 45 s (8 sections, the withheld read, 4 releases of 8 sweeps; the build's smoke read 5
#   sections in 3.5 s and 6.7 s)
#   time     45 s
#   train   480 s   TRAIN_S = 450 s from its own start; LAPS = ⌊450,000 / P_A⌋; P_B = 4 P_A
#   release 150 s   internal 120 s, the free set first, then the marks
#   text     40 s   internal 20 s
#   rules     5 s
# 45 + 45 + 45 + 480 + 150 + 40 + 5 = 810 ≤ 900.
set -u
ROOT=$ROOT
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
C=$W/.local/run/crib-closure
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/dispersing/crib9; M="python3 -I $W/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
DECL="32 4 8 2 32 2 16"
TRAIN_S=450; RELEASE_S=120; TEXT_S=20
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 600 9 || { echo "LOCK_BUSY"; exit 75; }
START=$(date +%s)
el() { echo $(( $(date +%s) - START )); }
T="$G/UNITS0 $(sha $G/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD.txt $(sha $C/HELD.txt) $K $(sha $K)"
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) train=$(sha $C/TRAIN.txt) held=$(sha $C/HELD.txt)"
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
for P in "A 1 45" "B 2 45"; do
  set -- $P
  $M crib9 timeout $3 $BIN parity complete-language parity-field $T $DECL 8 8 $2 4 8 > $O/parity$1.log 2>&1
  grep -q FIELD_PARITY_DONE $O/parity$1.log && ! grep FIELD_PARITY_DONE $O/parity$1.log | grep -qE '_unequal=[1-9]' \
    || { echo "STOP parity$1 at=$(el) $(grep -m1 -E 'unequal=[1-9]|rror|refused|FIELD_PARITY_DONE' $O/parity$1.log) $(tail -2 $O/parity$1.log | tr '\n' ' ')"; kill $SMI; exit 1; }
  echo "PARITY$1 at=$(el) $(grep -E 'FIELD_PARITY_DONE|FIELD_CARD |MEASURE' $O/parity$1.log | tr '\n' ' ')"
done
$M crib9 timeout 45 $BIN time complete-language time-field $T $DECL 16 8 4 64 > $O/time.log 2>&1
PA=$(num FIELD_TIME_LAP $O/time.log projection_ms)
[ -n "$PA" ] && [ $PA -gt 0 ] || { echo "NO_PROJECTION at=$(el) $(tail -3 $O/time.log | tr '\n' ' ')"; kill $SMI; exit 1; }
PB=$((PA * 4)); LAPS=$((TRAIN_S * 1000 / PA)); [ $LAPS -ge 1 ] || { echo "NO_LAP_FITS P_A=$PA"; kill $SMI; exit 1; }
echo "TIME at=$(el) $(grep -E 'FIELD_TIME_LAP|FIELD_TIME_PAIRS|FIELD_TIME_RELEASES|FIELD_CARD |MEASURE' $O/time.log | tr '\n' ' ') P_A=$PA P_B=$PB laps=$LAPS"
rm -rf $O/train
$M crib9 timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $T $DECL $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? at=$(el) $(grep -E 'FIELD_DECLARATION|FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_LAPS_HELD|FIELD_CARD |MEASURE|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-14000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE at=$(el)"; kill $SMI; exit 1; }
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT at=$(el)"
rm -rf $O/release
$M crib9 timeout $((RELEASE_S + 30)) $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $C/HELD.txt $(sha $C/HELD.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE |FIELD_RELEASE_RECEIPTS|FIELD_CARD |MEASURE|rror' $O/release.log | tr '\n' ' ' | cut -c1-2500) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log)"
echo "RELEASE_SWEEPS $(grep FIELD_RELEASE_SWEEP $O/release.log | awk '{ s = $2 } s != last { if (line) print line; last = s } { line = $0 } END { print line }' | tr '\n' ' ')"
$M crib9 timeout $((TEXT_S + 20)) $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $C/HELD.txt $(sha $C/HELD.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE_TEXT|MEASURE' $O/text.log | tr '\n' ' ')"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
timeout 5 python3 -I $W/tools/gsm8k/written_rules.py $C/HELD.txt $C/TRAIN.txt $O/release > $O/rules.txt 2>&1
echo "RULES at=$(el) $(head -1 $O/rules.txt)"
