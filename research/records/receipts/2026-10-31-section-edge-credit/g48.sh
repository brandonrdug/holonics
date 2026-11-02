#!/usr/bin/env bash
# Record §45's cause read: the GSM8K pair learner at rate 2^(-8) (rate bits 8, against 7) for 40 laps
# from C′'s founding keys at 160 streams: if the accepted steps' cross-section harm is their size, the
# plateau of laps 18 to 30 and its training-code rise go with the half rate. Projection 40 x 18.4 s =
# 736 s; deadline 800 s. The receipt at laps 20 and 40.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-44a}
E=$R/race/g48; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ)"
O=$E/pair8; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py pair8 timeout 800 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower $U $US \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 40 8 $O > $O.log 2>&1
echo "RUN_END pair8 rc=$? $(grep -E 'TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
for lap in 19 39; do
  S=$O/STATE.$lap
  [ -f "$S" ] || { echo "RECEIPT lap $((lap+1)) absent"; continue; }
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
    python3 -I $R/measure.py flux-$lap timeout 300 $BIN read complete-language read-tower-race $S $(sha $S) \
    $G/DEV.units $(sha $G/DEV.units) $G/PROMPTS6.units $(sha $G/PROMPTS6.units) 24 128 $E/flux-pair8-$lap > $E/flux-pair8-$lap.log 2>&1
  for kind in FREE:512 MARKS:16; do
    k=${kind%%:*}; m=${kind#*:}
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 -E TOWER_PROMPT_SEPARATOR=31 \
      python3 -I $R/measure.py $k-$lap timeout 300 $BIN release complete-language release-tower-classes $S $(sha $S) \
      $G/$k.prompts.units $(sha $G/$k.prompts.units) $G/GKEYS $(sha $G/GKEYS) $m 1 $E/$k-pair8-$lap > $E/$k-pair8-$lap.log 2>&1
  done
  echo "RECEIPT lap $((lap+1)) done"
done
