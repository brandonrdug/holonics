#!/usr/bin/env bash
# Record §44, acceptance 74 and 75's cost read: the card against the host on the GSM8K units with
# participation from level 0 (section 256) beside packets, passage, heading and every-level credit, with
# pair contacts (24 streams, 32 sections; deadline 600 s, the §35 parity ran 72 s and participation
# now reads at six levels); then one lap at 160 streams from C′'s founding keys (unmeasured: §34's
# every-level participation cost 8.2 times its plain lap, the GSM8K pair lap 18.4 s at most: 150 s,
# deadline 300 s), its device peak and the receipt.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-44a}
E=$R/race/g45; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR
export TOWER_PARTICIPATION_FROM=0 TOWER_PARTICIPATION_SECTION=256
echo "BIN=$(sha $BIN) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity-pa0 timeout 600 $BIN parity-units-founded $U $US $G/TRAIN.bytes $(sha $G/TRAIN.bytes) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level-pair-participating > $E/parity-pa0.log 2>&1
echo "PARITY_PA0 rc=$? $(grep -E 'TOWER_PARTICIPATION|TOWER_PARITY_DONE|MEASURE|rror' $E/parity-pa0.log | tr '\n' ' ')"
grep -q 'gradient_unequal=0 learners_unequal=0' $E/parity-pa0.log || { echo "PARITY_FAILED stop"; exit 0; }
O=$E/pa0; rm -rf $O
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
VRAM=$!
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py pa0-lap timeout 300 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-participating-pair-unit-tower $U $US \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 1 7 $O > $O.log 2>&1
echo "RUN_END pa0-lap rc=$? $(grep -E 'TOWER_PARTICIPATION|TOWER_SECTION pass=0 section=(32|64) |TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | sed 's/train_code=[0-9]* dev_code=[0-9]* grain_bits=20//' | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $O.vram | tail -1)"
