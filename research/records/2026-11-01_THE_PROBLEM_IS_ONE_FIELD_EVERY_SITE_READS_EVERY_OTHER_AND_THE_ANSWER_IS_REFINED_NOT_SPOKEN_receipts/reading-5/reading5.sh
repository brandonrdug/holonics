#!/usr/bin/env bash
# The field's fifth reading, after §15's repairs (the answer's boundary follows its content; the card's contact read a
# tile of keys a block, through the exponential's resident face, in carriers as wide as their terms): reading 1's
# declaration and data (D 32, H 4, n 8, still 2, f 32, K 2, SECTION 16, RATE 8), train-field from the founding over
# LAPS laps, release-field from the last state (128 held problems, the free releases first, then the marks),
# release-field-text for held problems 0..2.
#   reading5.sh TIME_A TIME_B
# Every bound is derived here, before launch, from time-field's projections in the logs TIME_A and TIME_B (the
# waiting standard), and none is raised. The reading holds 900 s. [agent-inferred, November 1] The release takes its
# last third (RELEASE_S = 300 s): under the boundary law a release reads its whole opening extent until its content
# reaches its end, so its sweeps cost the opening's (time-field's free_sweep_ms, marks_sweep_ms, an upper bound a
# sweep) and their count is the trained field's own, which no founding read projects; the free set, the claim, runs
# first. The text read takes 30 s and 30 s are kept for the processes' starts and the state's write; the training
# takes the rest (TRAIN_S = 540 s), LAPS = ⌊TRAIN_S / P_A⌋ whole laps at the projection's upper end P_A, with A_MS = P_A
# and B_MS = P_B bounding a lap before and after a growth. The trainer applies its bounds itself and, past any, rests
# as STATE.stopped (FIELD_STOPPED), reported incomplete and still released. Each release applies its own deadline
# (STOP_MS): past it no further sweep runs and the answers are returned as released, the sets stopped counted open.
# The outer timeouts (each deadline + 30 s) only guard a command that does not stop. Nothing is relaunched.
set -u
TA=$1; TB=$2
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/reading-5
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
PA=$(num FIELD_TIME_LAP $TA projection_ms); PB=$(num FIELD_TIME_LAP $TB projection_ms)
[ -n "$PA" ] && [ -n "$PB" ] || { echo "NO_PROJECTION"; exit 1; }
RELEASE_S=300; TEXT_S=30; TRAIN_S=540
LAPS=$((TRAIN_S * 1000 / PA)); [ $LAPS -ge 1 ] || { echo "NO_LAP_FITS P_A=$PA"; exit 1; }
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) P_A=$PA P_B=$PB laps=$LAPS train_s=$TRAIN_S release_s=$RELEASE_S text_s=$TEXT_S free_sweep_ms=$(num FIELD_TIME_RELEASES $TB free_sweep_ms) marks_sweep_ms=$(num FIELD_TIME_RELEASES $TB marks_sweep_ms)"
rm -rf $O/train
timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) \
    $K $(sha $K) 32 4 8 2 32 2 16 $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? $(grep -E 'FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_CARD|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-6000)"
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
