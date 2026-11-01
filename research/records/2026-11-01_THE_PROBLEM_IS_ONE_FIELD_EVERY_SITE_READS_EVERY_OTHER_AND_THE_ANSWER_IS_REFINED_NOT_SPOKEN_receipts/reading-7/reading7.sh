#!/usr/bin/env bash
# The field's seventh reading, after §17's law (the opening carries each site's strand contacts, x⁰_t = E(u_t) +
# E₋(u_(t−1)) + E₊(u_(t+1)), the contact encodings founded at zero): train-field from the founding (a learner saved
# before the law has no contact encodings and is refused), release-field from the last state (128 held problems, the
# free releases first, then the marks), release-field-text for held problems 0..2. Reading 1's declaration and data
# (D 32, H 4, n 8, still 2, f 32, K 2, SECTION 16, RATE 8) and keys; only the opening changed.
#   reading7.sh TIME_A TIME_B
# P_A and P_B are read from checks7.sh's time-field logs (the kernels changed, so reading 5's do not stand). Every bound
# is derived here, before launch, and none is raised. The reading holds 900 s: the training 600 s (TRAIN_S), the
# release 240 s (RELEASE_S), the text read 30 s and 30 s for the processes' starts and the state's write, the sixth
# reading's partition, under which its release finished (free set 44 s, marks 158 s). LAPS is a count bound,
# ⌊TRAIN_S / L⌋ with L the shortest lap the sixth reading measured at this width (consecutive FIELD_HELD times in its
# train log, the lap with its withheld and held reads): the trainer starts a lap only while elapsed + P_A (P_B after
# its one growth) stays within TRAIN_S, so the time decides the laps and the count never binds before it. Past any
# bound the trainer rests as STATE.stopped (FIELD_STOPPED), reported incomplete and still released. Each release
# applies its own deadline; the outer timeouts (each deadline + 30 s) only guard a command that does not stop.
# Nothing is relaunched.
set -u
TA=$1; TB=$2
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; P=$W/.local/run/reading-6; O=$W/.local/run/reading-7
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
PA=$(num FIELD_TIME_LAP $TA projection_ms); PB=$(num FIELD_TIME_LAP $TB projection_ms)
[ -n "$PA" ] && [ -n "$PB" ] || { echo "NO_PROJECTION"; exit 1; }
L=$(grep -E '^FIELD_HELD lap=[0-9]' $P/train.log | sed -n 's/.* ms=\([0-9]*\).*/\1/p' | awk 'NR > 1 { d = $1 - p; if (m == 0 || d < m) m = d } { p = $1 } END { print m + 0 }')
[ "$L" -gt 0 ] || { echo "NO_LAP_MEASURED"; exit 1; }
RELEASE_S=240; TEXT_S=30; TRAIN_S=600
LAPS=$((TRAIN_S * 1000 / L)); [ $LAPS -ge 1 ] && [ $((PA)) -le $((TRAIN_S * 1000)) ] || { echo "NO_LAP_FITS L=$L P_A=$PA"; exit 1; }
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) P_A=$PA P_B=$PB L=$L laps=$LAPS train_s=$TRAIN_S release_s=$RELEASE_S text_s=$TEXT_S"
rm -rf $O/train
timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) \
    $K $(sha $K) 32 4 8 2 32 2 16 $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? $(grep -E 'FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_CARD|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-12000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE"; kill $SMI; exit 1; }
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT"
rm -rf $O/release
timeout $((RELEASE_S + 30)) $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? $(grep -E 'FIELD_RELEASE |FIELD_CARD|rror' $O/release.log | tr '\n' ' ' | cut -c1-1200) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log) batch_refused=$(grep -c FIELD_RELEASE_BATCH_REFUSED $O/release.log)"
echo "RELEASE_SWEEPS $(grep FIELD_RELEASE_SWEEP $O/release.log | awk '{ s = $2 } s != last { if (line) print line; last = s } { line = $0 } END { print line }' | tr '\n' ' ')"
timeout $((TEXT_S + 30)) $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? $(grep FIELD_RELEASE_TEXT $O/text.log)"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
