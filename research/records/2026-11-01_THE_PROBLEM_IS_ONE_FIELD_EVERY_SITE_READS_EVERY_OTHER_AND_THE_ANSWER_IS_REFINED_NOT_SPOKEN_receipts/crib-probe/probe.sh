#!/usr/bin/env bash
# The crib probe (§18): whether the field reads a number across a question at all, on the crib terrain
# (`crib-terrain`: questions of 48 to 79 meaningless words with two or three numbers, answers that sum them in
# the question's order, so the answer's numbers are read from the question and nowhere else), under §18's
# laws (the contact founded as the pair's likeness, its probe and key at unit power within a head, no site
# meeting itself, the release refined). Reading 7's declaration, keys, section and rate (D 32, H 4, n 8, still 2 of 4 ring
# sets, f 32, K 2, SECTION 16, RATE 8); only the terrain differs.
#   probe.sh
# 0. The key file's bytes (the founding's draws): a degenerate stream founds every word alike (§18).
# 1. The terrain: 4,096 training problems and 128 held, seed 20261101.
# 2. The card against the host on the terrain's sections (parity-field, as reading 7's checks, without and
#    with one growth); a stop at the first unequal read ends the probe there.
# 3. time-field on the terrain: P_A, the lap's projection; P_B, after one growth, is four times it (reading 7
#    measured 1.76 times at the grown width), so the bound after a growth never stops a lap the card can run.
# 4. train-field from the founding for TRAIN_S = 300 s, laps from P_A as reading 7's; release-field on the 128
#    held problems for RELEASE_S = 150 s (sweeps the codec's answer extent); release-field-text on held
#    problems 0..2 for 30 s.
# 5. The written rules on the release against the terrain's own passages (c_from_question against c_foil).
# The probe holds 900 s at most: parity 120 s and 180 s (the host reads every section beside the card, and the
# grown field twice the width), time 60 s, training 300 s, release 150 s, text 30 s, the rest the processes'
# starts; parity's releases run 8 sweeps, so the refinement's rereads are compared too. Every bound is fixed here before launch and none is raised; past one, a
# command stops and its partial evidence is reported incomplete. Nothing is relaunched.
set -u
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/crib
sha() { sha256sum "$1" | cut -c1-64; }
num() { grep -m1 "$1" "$2" | sed -n "s/.* $3=\([0-9]*\).*/\1/p"; }
DECL="32 4 8 2 32 2 16"
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) board=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader)"
python3 -I -c "import sys, collections; b = open(sys.argv[1], 'rb').read(1 << 20); c = collections.Counter(b); w = collections.Counter(b[i:i + 4] for i in range(0, len(b), 4)); print('KEYS_BYTES distinct', len(c), 'least', min(c.values()), 'most', max(c.values()), 'words', len(w), 'of', len(b) // 4)" $K
[ -e $O/TRAIN.txt ] || $BIN train complete-language crib-terrain 20261101 4096 128 $O/TRAIN.txt $O/HELD.txt > $O/terrain.log 2>&1
T="$G/UNITS0 $(sha $G/UNITS0) $O/TRAIN.txt $(sha $O/TRAIN.txt) $O/HELD.txt $(sha $O/HELD.txt) $K $(sha $K)"
echo "TERRAIN $(grep CRIB_TERRAIN $O/terrain.log) train=$(sha $O/TRAIN.txt) held=$(sha $O/HELD.txt)"
for P in "A 1 120" "B 2 180"; do
  set -- $P
  timeout $3 $BIN parity complete-language parity-field $T $DECL 8 8 $2 4 8 > $O/parity$1.log 2>&1
  grep -q FIELD_PARITY_DONE $O/parity$1.log && ! grep FIELD_PARITY_DONE $O/parity$1.log | grep -qE '_unequal=[1-9]' \
    || { echo "STOP parity$1 $(grep -m1 -E 'unequal=[1-9]|rror|refused|FIELD_PARITY_DONE' $O/parity$1.log)"; exit 1; }
  echo "PARITY$1 $(grep FIELD_PARITY_DONE $O/parity$1.log)"
done
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 500 > $O/smi.csv &
SMI=$!
timeout 60 $BIN time complete-language time-field $T $DECL 16 8 4 64 > $O/time.log 2>&1
PA=$(num FIELD_TIME_LAP $O/time.log projection_ms)
[ -n "$PA" ] || { echo "NO_PROJECTION $(tail -3 $O/time.log | tr '\n' ' ')"; kill $SMI; exit 1; }
PB=$((PA * 4))
TRAIN_S=300; RELEASE_S=150; TEXT_S=30
LAPS=$((TRAIN_S * 1000 / PA)); [ $LAPS -ge 1 ] || { echo "NO_LAP_FITS P_A=$PA"; kill $SMI; exit 1; }
echo "TIME $(grep -E 'FIELD_TIME_LAP|FIELD_TIME_RELEASES' $O/time.log | tr '\n' ' ') P_A=$PA P_B=$PB laps=$LAPS"
rm -rf $O/train
timeout $((TRAIN_S + 30)) $BIN train complete-language train-field $T $DECL $LAPS 8 $PA $PB $((TRAIN_S * 1000)) $O/train > $O/train.log 2>&1
echo "TRAIN_END rc=$? $(grep -E 'FIELD_DECLARATION|FIELD_LAP|FIELD_UNSEEN|FIELD_HELD|FIELD_GROW|FIELD_STOPPED|FIELD_CARD|rror|refused' $O/train.log | grep -v FIELD_SECTION | tr '\n' ' ' | cut -c1-12000)"
if [ -e $O/train/STATE.stopped ]; then S=STATE.stopped; else S=$(ls $O/train | grep -E '^STATE\.[0-9]+$' | sort -t. -k2 -n | tail -1); fi
[ -n "$S" ] || { echo "NO_STATE"; kill $SMI; exit 1; }
EXT=$(head -1 $O/train/CODEC | cut -d' ' -f2)
echo "RELEASE_FROM $S sweeps=$EXT"
rm -rf $O/release
timeout $((RELEASE_S + 30)) $BIN train complete-language release-field $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $O/HELD.txt $(sha $O/HELD.txt) 128 $EXT $((RELEASE_S * 1000)) $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? $(grep -E 'FIELD_RELEASE |FIELD_CARD|rror' $O/release.log | tr '\n' ' ' | cut -c1-1200) refused=$(grep -c FIELD_RELEASE_REFUSED $O/release.log)"
echo "RELEASE_SWEEPS $(grep FIELD_RELEASE_SWEEP $O/release.log | awk '{ s = $2 } s != last { if (line) print line; last = s } { line = $0 } END { print line }' | tr '\n' ' ')"
timeout $((TEXT_S + 30)) $BIN train complete-language release-field-text $O/train/$S $(sha $O/train/$S) $O/train/CODEC $(sha $O/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $O/HELD.txt $(sha $O/HELD.txt) 3 $EXT $((TEXT_S * 1000)) > $O/text.log 2>&1
echo "TEXT_END rc=$? $(grep FIELD_RELEASE_TEXT $O/text.log)"
kill $SMI
echo "BOARD_PEAK_MIB $(cut -d, -f1 $O/smi.csv | sort -n | tail -1) baseline=$(head -1 $O/smi.csv | cut -d, -f1)"
python3 -I $W/tools/gsm8k/written_rules.py $O/HELD.txt $O/TRAIN.txt $O/release 2>&1 | head -3
