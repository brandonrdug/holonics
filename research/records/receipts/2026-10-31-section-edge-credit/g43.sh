#!/usr/bin/env bash
# Record §43 (with §42's acceptance 72): GSM8K alone. The card against the host for the paired working
# declaration on the GSM8K units (24 streams, 32 sections; deadline 300 s); then 20 laps of each
# declaration at 160 streams from C′'s founding keys: rectifying, pair contacts, pair contacts with the
# founded split (66 sections a lap; projection from the unit passage's largest measured sections:
# 1,320 x 0.248 s = 327 s, x 0.283 s = 374 s, x 0.56 s = 740 s; deadlines 400, 450, 900 s). Then the
# receipt at laps 5, 10 and 20 of each: the questions' flux into their answers (six development
# problems; 300 s) and the written-rule releases for 128 development problems (free at agree 1, 512
# units; each calculation at agree 1, 16 units; 300 s each).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-43a}
E=$R/race/g43; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_PARTICIPATION_SECTION TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR
echo "BIN=$(sha $BIN) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity-split timeout 300 $BIN parity-units-founded $U $US $G/TRAIN.bytes $(sha $G/TRAIN.bytes) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level-split > $E/parity-split.log 2>&1
echo "PARITY_SPLIT rc=$? $(grep -E 'TOWER_PARITY_DONE|TOWER_PARITY_SPLIT_DONE|MEASURE|rror' $E/parity-split.log | tr '\n' ' ')"
SPLIT_OK=0; grep -q 'gradient_unequal=0 learners_unequal=0' $E/parity-split.log && grep -q 'splits_unequal=0' $E/parity-split.log && SPLIT_OK=1
for run in "rect:train-two-ladder-stacked-news-heading-credited-every-level-unit-tower:400" "pair:train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower:450" "split:train-two-ladder-stacked-news-heading-credited-every-level-split-unit-tower:900"; do
  name=${run%%:*}; rest=${run#*:}; route=${rest%%:*}; limit=${rest#*:}
  if [ $name = split ] && [ $SPLIT_OK = 0 ]; then echo "SPLIT skipped: parity"; continue; fi
  O=$E/$name; rm -rf $O
  nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
  VRAM=$!
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py $name timeout $limit $BIN train complete-language $route $U $US \
    $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
    $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 20 7 $O > $O.log 2>&1
  echo "RUN_END $name rc=$? $(grep -E 'TOWER_PASS |TOWER_PAIRED PAIRED |TOWER_CARD|MEASURE|rror' $O.log | sed 's/train_code=[0-9]* dev_code=[0-9]* grain_bits=20//' | tr '\n' ' ')"
  kill $VRAM; echo "VRAM_PEAK_MIB $name=$(sort -n $O.vram | tail -1)"
  for lap in 4 9 19; do
    S=$O/STATE.$lap
    [ -f "$S" ] || { echo "RECEIPT_$name lap $((lap+1)) absent"; continue; }
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
      python3 -I $R/measure.py flux-$name-$lap timeout 300 $BIN read complete-language read-tower-race $S $(sha $S) \
      $G/DEV.units $(sha $G/DEV.units) $G/PROMPTS6.units $(sha $G/PROMPTS6.units) 24 128 $E/flux-$name-$lap > $E/flux-$name-$lap.log 2>&1
    echo "FLUX_$name lap $((lap+1)) rc=$? $(grep -E 'TOWER_RACE_FLUX_HEAD|TOWER_RACE_FLUX prompt|MEASURE|rror' $E/flux-$name-$lap.log | tr '\n' ' ')"
    for kind in FREE:512 MARKS:16; do
      k=${kind%%:*}; n=${kind#*:}
      systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 -E TOWER_PROMPT_SEPARATOR=31 \
        python3 -I $R/measure.py $k-$name-$lap timeout 300 $BIN release complete-language release-tower-classes $S $(sha $S) \
        $G/$k.prompts.units $(sha $G/$k.prompts.units) $G/GKEYS $(sha $G/GKEYS) $n 1 $E/$k-$name-$lap > $E/$k-$name-$lap.log 2>&1
      echo "RELEASE_$k $name lap $((lap+1)) rc=$? $(grep -E 'CLASSES_RELEASE_DONE|MEASURE|rror' $E/$k-$name-$lap.log | tr '\n' ' ')"
    done
  done
done
