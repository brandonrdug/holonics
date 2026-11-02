#!/usr/bin/env bash
# Record §44, acceptance 75: 20 laps of the pair learner with participation from level 0 (section 256)
# on GSM8K at 160 streams from C′'s founding keys. A stated long run: projection 20 x 147.2 s (its
# measured lap with the run's opening) = 2,944 s, deadline 3,000 s; its value is the read of whether a
# question's particulars reach the answer's first step when the arrival levels read back over it.
# The receipt at laps 5, 10 and 20 (flux and written rules; 300 s each).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-44a}
E=$R/race/g46; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR
export TOWER_PARTICIPATION_FROM=0 TOWER_PARTICIPATION_SECTION=256
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ)"
O=$E/pa0; rm -rf $O
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 1000 > $O.vram &
VRAM=$!
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py pa0 timeout 3000 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-participating-pair-unit-tower $U $US \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 20 7 $O > $O.log 2>&1
echo "RUN_END pa0 rc=$? $(grep -E 'TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $O.vram | tail -1)"
for lap in 4 9 19; do
  S=$O/STATE.$lap
  [ -f "$S" ] || { echo "RECEIPT lap $((lap+1)) absent"; continue; }
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
    python3 -I $R/measure.py flux-$lap timeout 300 $BIN read complete-language read-tower-race $S $(sha $S) \
    $G/DEV.units $(sha $G/DEV.units) $G/PROMPTS6.units $(sha $G/PROMPTS6.units) 24 128 $E/flux-pa0-$lap > $E/flux-pa0-$lap.log 2>&1
  for kind in FREE:512 MARKS:16; do
    k=${kind%%:*}; m=${kind#*:}
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 -E TOWER_PROMPT_SEPARATOR=31 \
      python3 -I $R/measure.py $k-$lap timeout 300 $BIN release complete-language release-tower-classes $S $(sha $S) \
      $G/$k.prompts.units $(sha $G/$k.prompts.units) $G/GKEYS $(sha $G/GKEYS) $m 1 $E/$k-pa0-$lap > $E/$k-pa0-$lap.log 2>&1
  done
  echo "RECEIPT lap $((lap+1)) done"
done
