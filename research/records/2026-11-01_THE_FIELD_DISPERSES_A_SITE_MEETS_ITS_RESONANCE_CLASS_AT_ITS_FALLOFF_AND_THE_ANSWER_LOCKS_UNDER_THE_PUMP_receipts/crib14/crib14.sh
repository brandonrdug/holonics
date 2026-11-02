#!/usr/bin/env bash
# crib14: the located clock (§16.15–§16.16): the pace located by loop closure at each lap boundary, never deposited; the
# (the key's foil), the lock's temperature deposited, growth held until the withheld code falls, the held step read
# on context regions too; moments, clock, echoes and the complex merge as §15.7. The crib terrain (seed 20261101,
# 4,096 training problems and 128 held), reading 8's keys, section and rate, D 32, H 5, n 8, f 32, K 2. Bar (§7): at
# least 24 of 126 first calculations from the question, above its foil. Receipts add the review's three reads:
# FIELD_ROWS_HELD (the question's share and current at the held answer sites, the soft near share), FIELD_COVECTORS
# (closure against face on each lap's first section) beside FIELD_LAP's accepted and refused steps.
# crib14's declaration (§16.16): K 3, 27 laps, FIELD_CLOCK=located, the early stop after lap 9; every lap bounded by the
# time read's upper lap projection (P_A; a slower lap stops the run, reported incomplete); the run's deadline 75 minutes
# (an outer timeout in the launch); receipts at each boundary FIELD_CLOCK, FIELD_PEAKS, FIELD_BOUNDARY.
# The workload is fixed: 27 laps. Brandon lifted the night's time limits (05:30Z); the slots follow the projection
# with room. The partition, fixed before launch from the card's measured reads (each slot its command's outer
# timeout; nothing raised or relaunched):
#   time      30 s   (measured 3.6 s); the lap's upper projection 34.0-35.7 s at 48 sections (19.9-20.2 s at size),
#                    whose context term is counted on top of sections that already hold it (an upper bound)
#   train    27 × P_A plus 60 s (P_A the time read's upper lap projection)
#   release  120 s   internal 90 s (projected 22.0 s)
#   text      40 s   internal 20 s
#   rules      5 s
set -u
ROOT=<root>
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
C=$W/.local/run/crib-closure
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/dispersing/crib14; M="python3 -I $W/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
DECL="32 5 8 2 32 3 16"; SMALL=$W/.local/run/crib-small; LAPS=27
RELEASE_S=90; TEXT_S=20
mkdir -p $O
# The memory line: the run's measured peak resident set is about 1 GiB (card parity and training at GROW 1-2);
# launch only where at least 4 GiB stays free beside it.
AVAIL=$(free -m | awk '/^Mem:/{print $7}')
echo "MEMORY available_mib=$AVAIL projected_peak_mib=1100"
[ "$AVAIL" -ge $((1100 + 4096)) ] || { echo "LOW_MEMORY available_mib=$AVAIL"; exit 1; }
exec 9>$ROOT/.local/gpu.lock
flock -w 600 9 || { echo "LOCK_BUSY"; exit 75; }
START=$(date +%s)
el() { echo $(( $(date +%s) - START )); }
T="$G/UNITS0 $(sha $G/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD.txt $(sha $C/HELD.txt) $K $(sha $K)"
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader) train=$(sha $C/TRAIN.txt) held=$(sha $C/HELD.txt)"
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
# No parity in the run: this binary (its sha printed above) is the one parity-checked at both widths
# before launch (receipts beside the record).
$M crib14 timeout 30 $BIN time complete-language time-field $T $DECL 16 8 4 64 > $O/time.log 2>&1
PA=$(num FIELD_TIME_LAP $O/time.log projection_ms)
[ -n "$PA" ] && [ $PA -gt 0 ] || { echo "NO_PROJECTION at=$(el) $(tail -3 $O/time.log | tr '\n' ' ')"; kill $SMI; exit 1; }
PB=$PA; TRAIN_S=$((4500 - 60 - 150 - 60))
echo "TIME at=$(el) $(grep -E 'FIELD_TIME_LAP|FIELD_TIME_PAIRS|FIELD_TIME_RELEASES|FIELD_CARD |MEASURE' $O/time.log | tr '\n' ' ') P_A=$PA P_B=$PB laps=$LAPS train_s=$TRAIN_S"
rm -rf $O/train
FIELD_CLOCK=located FIELD_PEAKS_EACH_LAP=1 $M crib14 timeout $((TRAIN_S + 60)) $BIN train complete-language train-field $T $DECL $LAPS 8 $PA $PA $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? at=$(el) $(grep -E 'FIELD_DECLARATION|FIELD_LAP|FIELD_UNSEEN|FIELD_HELD |FIELD_GROW|FIELD_STOPPED|FIELD_LAPS_HELD|FIELD_COVECTORS |FIELD_CARD |MEASURE|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-14000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE at=$(el)"; kill $SMI; exit 1; }
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT at=$(el)"
rm -rf $O/release
$M crib14 timeout $((RELEASE_S + 30)) $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $C/HELD.txt $(sha $C/HELD.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE |FIELD_RELEASE_RECEIPTS|FIELD_CARD |MEASURE|rror' $O/release.log | tr '\n' ' ' | cut -c1-2500) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log)"
echo "RELEASE_SWEEPS $(grep FIELD_RELEASE_SWEEP $O/release.log | awk '{ s = $2 } s != last { if (line) print line; last = s } { line = $0 } END { print line }' | tr '\n' ' ')"
$M crib14 timeout $((TEXT_S + 20)) $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $C/HELD.txt $(sha $C/HELD.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE_TEXT|MEASURE' $O/text.log | tr '\n' ' ')"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
timeout 5 python3 -I $W/tools/gsm8k/written_rules.py $C/HELD.txt $C/TRAIN.txt $O/release > $O/rules.txt 2>&1
echo "RULES at=$(el) $(head -1 $O/rules.txt)"
