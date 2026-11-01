#!/usr/bin/env bash
# The field's fourth reading, after §13's repairs (the release by resolution, the withheld problems read beside their
# neighbours, the rewritten card realization and its counted memory): reading 1's declaration and data (D 32, H 4, n 8,
# still 2, f 32, K 2, SECTION 16, RATE 8), train-field from the founding over LAPS laps, release-field from the last
# state (128 held problems, the free releases first, then the marks), release-field-text for held problems 0..2.
#   reading4.sh LAPS TRAIN_S A_MS B_MS RELEASE_S TEXT_S
# The releases' sweeps are bounded by the codec's open answer sites (S = EXT, read from the run's CODEC): every sweep
# releases a site of every open problem, so S = EXT lets every release end. Their time is bounded by RELEASE_S and
# TEXT_S, which each command applies itself (STOP_MS): past it no further sweep runs and the answers are returned as
# released, the sets stopped counted open (free_stopped, marks_stopped).
# Every bound is fixed before launch from time-field's projections (the waiting standard). A_MS and B_MS bound a lap
# before and after a growth and TRAIN_S the training; the trainer applies them itself and, past any, rests as
# STATE.stopped (FIELD_STOPPED), so a stopped training is reported incomplete and still releases. The outer timeout
# (TRAIN_S + 30 s for the stopped lap's withheld read and the state's write) only guards a trainer that does not stop.
# The outer timeouts of the releases (their deadlines + 30 s) only guard a command that does not stop. No bound is
# raised and nothing is relaunched.
set -u
LAPS=$1; TRAIN_S=$2; A_MS=$3; B_MS=$4; RELEASE_S=$5; TEXT_S=$6
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/reading-4
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
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT"
rm -rf $O/release
timeout $((RELEASE_S + 30)) $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? $(grep -E 'FIELD_RELEASE |FIELD_CARD|rror' $O/release.log | tr '\n' ' ' | cut -c1-1200) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log) batch_refused=$(grep -c FIELD_RELEASE_BATCH_REFUSED $O/release.log)"
timeout $((TEXT_S + 30)) $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? $(grep FIELD_RELEASE_TEXT $O/text.log)"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
