#!/usr/bin/env bash
# crib12: the crib probe under §15 with §15.9 (an open receiver hears every definite site): one row a head scored by its
# modes' locks, sharp classes, moments in the values, the clock ring set, the echoes, the complex merge. The crib terrain
# (seed 20261101, 4,096 training problems and 128 held, as §19's probe), reading 8's keys, section and rate, D 32,
# H 5 (two still, two turned, one clock), n 8, f 32, K 2, SECTION 16, RATE 8. Bar (§7): at least 24 of 126 first
# calculations from the question, above its foil.
# The workload is fixed: 27 laps (crib10's). Brandon granted 18 minutes (1,080 s) for the whole run. The partition,
# fixed here before launch from the card's measured reads (each slot its command's outer timeout; nothing raised or
# relaunched):
#   time      30 s   (measured 3.6 s); projected 27 laps at 31.4 s upper (48 sections) and the release at 19.6 s: 867 s
#   train    the lesser of 27 × P_A and 840 s, plus 30 s (P_A the time read's upper lap projection; measured at size
#                    about 20 s a lap, so 27 laps about 540 s; a train past its stop is reported incomplete)
#   release  120 s   internal 90 s (projected 45.7 s for 128 problems)
#   text      40 s   internal 20 s
#   rules      5 s
# 30 + 870 + 120 + 40 + 5 = 1,065 ≤ 1,080.
set -u
ROOT=$ROOT
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
C=$W/.local/run/crib-closure
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/dispersing/crib12; M="python3 -I $W/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
DECL="32 5 8 2 32 2 16"; SMALL=$W/.local/run/crib-small; LAPS=27
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
$M crib12 timeout 30 $BIN time complete-language time-field $T $DECL 16 8 4 64 > $O/time.log 2>&1
PA=$(num FIELD_TIME_LAP $O/time.log projection_ms)
[ -n "$PA" ] && [ $PA -gt 0 ] || { echo "NO_PROJECTION at=$(el) $(tail -3 $O/time.log | tr '\n' ' ')"; kill $SMI; exit 1; }
PB=$((PA * 4)); TRAIN_S=$(( (LAPS * PA + 999) / 1000 )); [ $TRAIN_S -le 840 ] || TRAIN_S=840
echo "TIME at=$(el) $(grep -E 'FIELD_TIME_LAP|FIELD_TIME_PAIRS|FIELD_TIME_RELEASES|FIELD_CARD |MEASURE' $O/time.log | tr '\n' ' ') P_A=$PA P_B=$PB laps=$LAPS train_s=$TRAIN_S"
rm -rf $O/train
$M crib12 timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $T $DECL $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? at=$(el) $(grep -E 'FIELD_DECLARATION|FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_LAPS_HELD|FIELD_CARD |MEASURE|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-14000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE at=$(el)"; kill $SMI; exit 1; }
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT at=$(el)"
rm -rf $O/release
$M crib12 timeout $((RELEASE_S + 30)) $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $C/HELD.txt $(sha $C/HELD.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE |FIELD_RELEASE_RECEIPTS|FIELD_CARD |MEASURE|rror' $O/release.log | tr '\n' ' ' | cut -c1-2500) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log)"
echo "RELEASE_SWEEPS $(grep FIELD_RELEASE_SWEEP $O/release.log | awk '{ s = $2 } s != last { if (line) print line; last = s } { line = $0 } END { print line }' | tr '\n' ' ')"
$M crib12 timeout $((TEXT_S + 20)) $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $C/HELD.txt $(sha $C/HELD.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? at=$(el) $(grep -E 'FIELD_RELEASE_TEXT|MEASURE' $O/text.log | tr '\n' ' ')"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
timeout 5 python3 -I $W/tools/gsm8k/written_rules.py $C/HELD.txt $C/TRAIN.txt $O/release > $O/rules.txt 2>&1
echo "RULES at=$(el) $(head -1 $O/rules.txt)"
