#!/usr/bin/env bash
# The field's sixth reading, after §16's repairs (the answer's extent is read once at the release's opening, where the
# earliest site whose void the field resolves is released and the sites past it leave the region; a lap starts only
# while the time left holds its bound; one growth a run): train-field continued from reading 5's rested learner
# (STATE.4, five laps, reading 1's declaration), release-field from the last state (128 held problems, the free
# releases first, then the marks), release-field-text for held problems 0..2.
#   reading6.sh [TIME_A TIME_B]
# The card realization is reading 5's (the kernels did not change; only the host's release law and the trainer's lap
# start did), so reading 5's parity and projections stand: P_A and P_B are read from its time-field logs TIME_A and
# TIME_B (default timeA7.log, timeB7.log). Every bound is derived here, before launch, and none is raised. The reading
# holds 900 s.
# [agent-inferred, November 1] The training takes 600 s (TRAIN_S), the release 240 s (RELEASE_S), the text read 30 s,
# and 30 s are kept for the processes' starts and the state's write. Why: reading 5's withheld code fell every lap
# (4.534 to 2.895) and its digits read beside their neighbours fell to the one-byte table's 3.46 without passing it,
# so the training is the read that has not finished; the release no longer reads the whole opening extent past its
# first sweep, so its sweeps cost the cut regions' (reading 5's 509 ms a sweep was the full extent's). LAPS is a count
# bound, ⌊TRAIN_S / L⌋ with L the longest lap reading 5 measured (consecutive FIELD_HELD times in its train.log, the
# lap with its withheld and held reads); the trainer itself starts a lap only while elapsed + P_A (P_B after a growth)
# stays within TRAIN_S, so the laps run are the time's, not this count's. Past any bound the trainer rests as
# STATE.stopped (FIELD_STOPPED), reported incomplete and still released. Each release applies its own deadline: past
# it no further sweep runs and the answers are returned as released, the sets stopped counted open. The outer
# timeouts (each deadline + 30 s) only guard a command that does not stop. Nothing is relaunched.
set -u
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
TA=${1:-$W/.local/run/timeA7.log}; TB=${2:-$W/.local/run/timeB7.log}
BIN=$W/target/release/examples/field_pass; P=$W/.local/run/reading-5; O=$W/.local/run/reading-6
FROM=$P/train/STATE.4
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
PA=$(num FIELD_TIME_LAP $TA projection_ms); PB=$(num FIELD_TIME_LAP $TB projection_ms)
[ -n "$PA" ] && [ -n "$PB" ] || { echo "NO_PROJECTION"; exit 1; }
[ -e $FROM ] || { echo "NO_STATE_FROM $FROM"; exit 1; }
L=$(grep -E '^FIELD_HELD lap=[0-9]' $P/train.log | sed -n 's/.* ms=\([0-9]*\).*/\1/p' | awk 'NR > 1 && $1 - p > m { m = $1 - p } { p = $1 } END { print m + 0 }')
[ "$L" -gt 0 ] || { echo "NO_LAP_MEASURED"; exit 1; }
RELEASE_S=240; TEXT_S=30; TRAIN_S=600
LAPS=$((TRAIN_S * 1000 / L)); [ $LAPS -ge 1 ] && [ $((PA)) -le $((TRAIN_S * 1000)) ] || { echo "NO_LAP_FITS L=$L P_A=$PA"; exit 1; }
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) from=reading-5/train/STATE.4 from_sha=$(sha $FROM) P_A=$PA P_B=$PB L=$L laps=$LAPS train_s=$TRAIN_S release_s=$RELEASE_S text_s=$TEXT_S"
rm -rf $O/train
timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) \
    $K $(sha $K) 32 4 8 2 32 2 16 $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train $FROM $(sha $FROM) > $O/train.log 2>&1
echo "TRAIN_END rc=$? $(grep -E 'FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_CARD|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-9000)"
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
