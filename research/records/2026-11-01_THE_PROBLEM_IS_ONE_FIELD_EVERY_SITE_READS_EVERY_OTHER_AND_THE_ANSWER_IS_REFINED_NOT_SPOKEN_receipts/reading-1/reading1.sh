#!/usr/bin/env bash
# The field's first reading (the design thread's brief of November 1, 04:37): train-field on the card from
# its founding (D 32, H 4, n 8, still 2, f 32, K 2, SECTION 16, LAPS 4, RATE 8; outer timeout 660 s; early
# stop past 165 s a lap at A or 330 s a lap after growth), release-field from the last STATE (128 held
# problems, S = 16; outer timeout 140 s), release-field-text for held problems 0..2 (S = 16; 60 s).
set -u
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/reading-1; M=$ROOT/.local/wt/section-edge/.local/run/measure.py
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader)"
rm -rf $O/train
( timeout 660 $BIN train complete-language train-field $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) \
    $K $(sha $K) 32 4 8 2 32 2 16 4 8 $O/train > $O/train.log 2>&1 & echo $! > $O/train.pid; wait $!; echo "rc=$?" > $O/train.rc ) &
TRAIN=$!
sleep 2
python3 -I $W/.local/run/watch.py $O/train.log $O/train.pid 165000 330000 > $O/watch.log 2>&1 &
WATCH=$!
wait $TRAIN
rm -f $O/train.pid
kill $WATCH 2>/dev/null
echo "TRAIN_END $(cat $O/train.rc) $(cat $O/watch.log) $(grep -E 'FIELD_LAP|FIELD_GROW|FIELD_CARD|rror|refused' $O/train.log | tr '\n' ' ' | cut -c1-1500)"
S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1)
[ -n "$S" ] || { echo "NO_STATE"; kill $SMI; exit 1; }
echo "RELEASE_FROM $S"
rm -rf $O/release
timeout 140 $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 128 16 $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? $(grep -E 'FIELD_RELEASE |FIELD_CARD|rror' $O/release.log | tr '\n' ' ' | cut -c1-800) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log)"
timeout 60 $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 3 16 > $O/text.log 2>&1
echo "TEXT_END rc=$?"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
