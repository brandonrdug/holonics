#!/usr/bin/env bash
# The field's eighth reading: GSM8K on §19's laws (the closure on the row's copy face, read over its ring set's
# heads) and §18's (the contact founded as the pair's likeness, unit power, no site meeting itself, the release
# refined). Reading 7's declaration, data and keys (UNITS0, TRAIN.txt, HELD128.txt, KEYS8; D 32, H 4, n 8, still 2,
# f 32, K 2, SECTION 16, RATE 8).
#   reading8.sh            (under an outer `timeout 900`)
# Order: parity A (the founded width) and B (grown by two, where each still ring set holds two copies and the closure
# reads over them), stopping at the first unequal read; time-field for P_A; train-field from the founding;
# release-field on the 128 held; release-field-text on held 0..2; the written rules.
# The partition, fixed here before launch (each slot is its command's outer timeout; nothing is raised or relaunched):
#   parity A 65 s   1 section, the held step's read on the withheld problems, 1 release of 4 sweeps (reading 7's A
#                   measured 4.9 s host a section, 31.4 s the withheld read, 11 s a release, about half the section's
#                   host time again for its mask reads; projected 55 s)
#   parity B 95 s   1 section, the withheld read, no release (B measured 9.7 s, 63.8 s; projected 85 s; the release's
#                   kernels are A's at another width)
#   time     20 s   reading 7's time-field (2.8 s wall)
#   train   540 s   TRAIN_S = 528 s from its own start (12 s for the start and the state's write); LAPS = ⌊528,000 /
#                   LAP_MS⌋ with LAP_MS = 48,838 ms, reading 7's largest lap at this width (its FIELD_HELD intervals,
#                   46.7 to 48.8 s), so time decides the laps; P_A from time-field, P_B = 4 P_A (the crib probe's rule;
#                   reading 7 measured 1.76 times at the grown width)
#   release 150 s   internal 138 s, the free set first, then the marks (reading 7: 30 s and 103 s before the refinement)
#   text     25 s   internal 15 s (reading 7: three releases in 832 ms)
#   rules     5 s
# 65 + 95 + 20 + 540 + 150 + 25 + 5 = 900.
set -u
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/reading-8
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
DECL="32 4 8 2 32 2 16"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
TRAIN_S=528; RELEASE_S=138; TEXT_S=15; LAP_MS=48838
LAPS=$((TRAIN_S * 1000 / LAP_MS))
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 600 9 || { echo "LOCK_BUSY"; exit 75; }
START=$(date +%s)
el() { echo $(( $(date +%s) - START )); }
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) laps=$LAPS train_s=$TRAIN_S release_s=$RELEASE_S text_s=$TEXT_S lap_ms=$LAP_MS"
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
for P in "A 1 1 65" "B 2 0 95"; do
  set -- $P
  python3 -I $ROOT/.local/wt/section-edge/.local/run/measure.py r8 timeout $4 $BIN parity complete-language parity-field $T $DECL 1 8 $2 $3 4 > $O/parity$1.log 2>&1
  grep -q FIELD_PARITY_DONE $O/parity$1.log && ! grep FIELD_PARITY_DONE $O/parity$1.log | grep -qE '_unequal=[1-9]' \
    || { echo "STOP parity$1 at=$(el) $(grep -m1 -E 'unequal=[1-9]|rror|refused|FIELD_PARITY_DONE' $O/parity$1.log) $(tail -2 $O/parity$1.log | tr '\n' ' ')"; kill $SMI; exit 1; }
  echo "PARITY$1 at=$(el) $(grep -E 'FIELD_PARITY_DONE|MEASURE' $O/parity$1.log | tr '\n' ' ')"
done
python3 -I $ROOT/.local/wt/section-edge/.local/run/measure.py r8 timeout 20 $BIN time complete-language time-field $T $DECL 16 8 4 16 > $O/time.log 2>&1
PA=$(num FIELD_TIME_LAP $O/time.log projection_ms)
[ -n "$PA" ] && [ $PA -le $((TRAIN_S * 1000)) ] || { echo "NO_PROJECTION at=$(el) $(tail -3 $O/time.log | tr '\n' ' ')"; kill $SMI; exit 1; }
PB=$((PA * 4))
echo "TIME at=$(el) $(grep -E 'FIELD_TIME_LAP|FIELD_TIME_RELEASES|MEASURE' $O/time.log | tr '\n' ' ') P_A=$PA P_B=$PB"
rm -rf $O/train
python3 -I $ROOT/.local/wt/section-edge/.local/run/measure.py r8 timeout 540 $BIN train complete-language train-field $T $DECL $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? at=$(el) $(grep -E 'FIELD_DECLARATION|FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_CARD|MEASURE|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-14000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE at=$(el)"; kill $SMI; exit 1; }
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT at=$(el)"
rm -rf $O/release
python3 -I $ROOT/.local/wt/section-edge/.local/run/measure.py r8 timeout 150 $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE |FIELD_CARD|MEASURE|rror' $O/release.log | tr '\n' ' ' | cut -c1-1500) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log)"
echo "RELEASE_SWEEPS $(grep FIELD_RELEASE_SWEEP $O/release.log | awk '{ s = $2 } s != last { if (line) print line; last = s } { line = $0 } END { print line }' | tr '\n' ' ')"
python3 -I $ROOT/.local/wt/section-edge/.local/run/measure.py r8 timeout 25 $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? at=$(el) $(grep -c FIELD_RELEASE_TEXT $O/text.log) texts $(grep MEASURE $O/text.log)"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
timeout 5 python3 -I $W/tools/gsm8k/written_rules.py $G/HELD128.txt $G/TRAIN.txt $O/release > $O/rules.txt 2>&1
echo "RULES at=$(el) $(head -1 $O/rules.txt)"
