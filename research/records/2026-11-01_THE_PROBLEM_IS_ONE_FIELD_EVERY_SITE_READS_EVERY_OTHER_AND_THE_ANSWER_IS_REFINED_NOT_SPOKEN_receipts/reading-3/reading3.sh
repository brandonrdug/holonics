#!/usr/bin/env bash
# The field's third reading, after the held step's bounded read and the trainer's own bounds (the record's §12) and the
# four repairs of §11: reading 1's declaration and data (D 32, H 4, n 8, still 2, f 32, K 2, SECTION 16, RATE 8),
# train-field from the founding over LAPS laps, release-field from the last state (128 held problems, S = 16),
# release-field-text for held problems 0..2.
#   reading3.sh LAPS TRAIN_S A_MS B_MS RELEASE_S TEXT_S
# Every bound is fixed before launch from time-field's projections (the waiting standard). A_MS and B_MS bound a lap
# before and after a growth and TRAIN_S the training; the trainer applies them itself and, past any, rests as
# STATE.stopped (FIELD_STOPPED), so a stopped training is reported incomplete and still releases. The outer timeout
# (TRAIN_S + 30 s for the stopped lap's withheld read and the state's write) only guards a trainer that does not stop.
# RELEASE_S and TEXT_S are the releases' deadlines. No bound is raised and nothing is relaunched.
set -u
LAPS=$1; TRAIN_S=$2; A_MS=$3; B_MS=$4; RELEASE_S=$5; TEXT_S=$6
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/reading-3
sha() { sha256sum "$1" | cut -c1-64; }
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) laps=$LAPS train_s=$TRAIN_S a_ms=$A_MS b_ms=$B_MS release_s=$RELEASE_S text_s=$TEXT_S"
rm -rf $O/train
timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) \
    $K $(sha $K) 32 4 8 2 32 2 16 $LAPS 8 $A_MS $B_MS $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? $(grep -E 'FIELD_LAP|FIELD_UNSEEN|FIELD_GROW|FIELD_STOPPED|FIELD_CARD|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-3000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE"; kill $SMI; exit 1; }
echo "RELEASE_FROM $S"
rm -rf $O/release
timeout $RELEASE_S $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 128 16 $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? $(grep -E 'FIELD_RELEASE |FIELD_CARD|rror' $O/release.log | tr '\n' ' ' | cut -c1-800) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log) batch_refused=$(grep -c FIELD_RELEASE_BATCH_REFUSED $O/release.log)"
timeout $TEXT_S $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 3 16 > $O/text.log 2>&1
echo "TEXT_END rc=$?"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
