#!/usr/bin/env bash
# Record §45: the working declaration on GSM8K (pair contacts at rate 2^(-8)) continued from lap 40 for
# 40 more laps at 160 streams (projection 40 x 12.5 s, its largest measured lap = 500 s; deadline 560 s),
# the receipt every ten laps (laps 50, 60, 70, 80), the written rules read at four release draws (the key
# files GKEYS, GKEYS_b, _c, _d) so each count carries its spread.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-44a}
E=$R/race/g50; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
FROM=$R/race/g48/pair8/STATE
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION
echo "BIN=$(sha $BIN) FROM=$(sha $FROM) at=$(date -u +%FT%TZ)"
O=$E/pair8; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py pair8-80 timeout 560 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower $U $US \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 40 8 $O $FROM $(sha $FROM) > $O.log 2>&1
echo "RUN_END pair8-80 rc=$? $(grep -E 'TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
for lap in 9 19 29 39; do
  S=$O/STATE.$lap; n=$((lap+41))
  [ -f "$S" ] || { echo "RECEIPT lap $n absent"; continue; }
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
    python3 -I $R/measure.py flux-$n timeout 300 $BIN read complete-language read-tower-race $S $(sha $S) \
    $G/DEV.units $(sha $G/DEV.units) $G/PROMPTS6.units $(sha $G/PROMPTS6.units) 24 128 $E/flux-$n > $E/flux-$n.log 2>&1
  for keys in GKEYS GKEYS_b GKEYS_c GKEYS_d; do
    for kind in FREE:512 MARKS:16; do
      k=${kind%%:*}; m=${kind#*:}
      systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 -E TOWER_PROMPT_SEPARATOR=31 \
        python3 -I $R/measure.py $k-$n-$keys timeout 300 $BIN release complete-language release-tower-classes $S $(sha $S) \
        $G/$k.prompts.units $(sha $G/$k.prompts.units) $G/$keys $(sha $G/$keys) $m 1 $E/$k-$n-$keys > $E/$k-$n-$keys.log 2>&1
    done
  done
  echo "RECEIPT lap $n done"
done
