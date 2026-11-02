#!/usr/bin/env bash
# Record §43: the GSM8K pair learner continued from lap 20 for 20 more laps at 160 streams, read for
# the training code's rise from lap 18 (projection 20 x 18.4 s, its largest lap = 368 s; deadline
# 420 s); the receipt at laps 30 and 40 (flux and written rules; 300 s each).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-43a}
E=$R/race/g44; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
FROM=$R/race/g43/pair/STATE
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_PARTICIPATION_SECTION TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR
echo "BIN=$(sha $BIN) FROM=$(sha $FROM) at=$(date -u +%FT%TZ)"
O=$E/pair; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py pair40 timeout 420 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower $U $US \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 20 7 $O $FROM $(sha $FROM) > $O.log 2>&1
echo "RUN_END pair40 rc=$? $(grep -E 'TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
for lap in 9 19; do
  S=$O/STATE.$lap; name=pair; n=$((lap+21))
  [ -f "$S" ] || { echo "RECEIPT lap $n absent"; continue; }
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
    python3 -I $R/measure.py flux-$n timeout 300 $BIN read complete-language read-tower-race $S $(sha $S) \
    $G/DEV.units $(sha $G/DEV.units) $G/PROMPTS6.units $(sha $G/PROMPTS6.units) 24 128 $E/flux-$name-$((n-1)) > $E/flux-$name-$((n-1)).log 2>&1
  for kind in FREE:512 MARKS:16; do
    k=${kind%%:*}; m=${kind#*:}
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 -E TOWER_PROMPT_SEPARATOR=31 \
      python3 -I $R/measure.py $k-$n timeout 300 $BIN release complete-language release-tower-classes $S $(sha $S) \
      $G/$k.prompts.units $(sha $G/$k.prompts.units) $G/GKEYS $(sha $G/GKEYS) $m 1 $E/$k-$name-$((n-1)) > $E/$k-$name-$((n-1)).log 2>&1
  done
  echo "RECEIPT lap $n done"
done
