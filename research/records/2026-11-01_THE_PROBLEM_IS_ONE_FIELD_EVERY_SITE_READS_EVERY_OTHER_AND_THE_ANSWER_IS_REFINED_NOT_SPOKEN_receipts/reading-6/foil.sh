#!/usr/bin/env bash
# What the question tells the answer, read on the fifth and sixth readings' rested learners (§17): train-field with
# LAPS 0 continued from each state, which reads the held problems (FIELD_HELD lap=-1: the opening, the answer beside
# its neighbours, and the same answer beside the next problem's question, `foil`) and the withheld ones, and trains
# nothing. A reading only.
#   foil.sh
# [agent-inferred, November 1] Each read is projected at under 10 s (the sixth reading's opening reads took 834 ms for
# the held problems and 1,179 ms with the withheld; the foil adds one context read of the same size, and the card's
# opening and the codec's founding take a few seconds); the guard is 150 s a read, the six reads under 15 minutes
# with room. Nothing is relaunched or raised.
set -u
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass; O=$W/.local/run/reading-6/foil
sha() { sha256sum "$1" | cut -c1-64; }
mkdir -p $O
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ)"
for S in reading-5/train/STATE.0 reading-5/train/STATE.4 reading-6/train/STATE.0 reading-6/train/STATE.3 reading-6/train/STATE.5 reading-6/train/STATE.7; do
  F=$W/.local/run/$S; N=$(echo $S | tr / -)
  [ -e $F ] || { echo "FOIL $S absent"; continue; }
  rm -rf $O/$N
  start=$(date +%s%N)
  timeout 150 $BIN train complete-language train-field $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) \
    $K $(sha $K) 32 4 8 2 32 2 16 0 8 1 1 120000 $O/$N $F $(sha $F) > $O/$N.log 2>&1
  rc=$?
  echo "FOIL $S rc=$rc wall_ms=$(( ($(date +%s%N) - start) / 1000000 )) $(grep -E 'FIELD_HELD|FIELD_UNSEEN|rror' $O/$N.log | tr '\n' ' ')"
done
