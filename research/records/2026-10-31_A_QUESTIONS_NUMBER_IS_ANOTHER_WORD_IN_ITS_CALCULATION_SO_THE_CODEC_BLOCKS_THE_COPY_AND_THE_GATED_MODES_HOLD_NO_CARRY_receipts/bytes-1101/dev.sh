#!/usr/bin/env bash
# Between R0 and R1 under the card's lock: the development reads that project R1 and R2 (R1 one whole lap,
# deadline 180 s; R2 the first 48 sections of a lap, deadline 180 s), then acceptance 77's parity (the card
# against the host over 32 sections with the step read on the next section, TOWER_NEXT_SECTION=1): the working
# declaration on the committed units at rate 2^(-8), and on the bytes at 2^(-3) so that steps are halved and
# refused on the card; then the card suite.
set -u
W=$ROOT/.local/wt/bytes-1101
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run; G=$R/gsm8k; E=$R/race/bytes-1101; mkdir -p $E
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
sha() { sha256sum "$1" | cut -c1-64; }
LAPS=1 RECEIPT=0 bash $W/.local/run/brun.sh r1dev train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower u0 180
LAPS=1 RECEIPT=0 TOWER_LAP_SECTIONS=48 TOWER_PARTICIPATION_FROM=4 TOWER_PARTICIPATION_SECTION=128 bash $W/.local/run/brun.sh r2dev train-two-ladder-stacked-news-heading-credited-every-level-participating-pair-unit-tower u0 180
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION TOWER_NEXT_SECTION
B77=$R/bin/tower_pass-77a
echo "B77=$(sha $B77) at=$(date -u +%FT%TZ)"
for run in "units:$U:8" "bytes:$G/UNITS0:3"; do
  name=${run%%:*}; rest=${run#*:}; u=${rest%%:*}; rate=${rest#*:}
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_NEXT_SECTION=1 \
    python3 -I $R/measure.py parity77-$name timeout 300 $B77 parity-units-founded $u $(sha $u) $G/TRAIN.bytes $(sha $G/TRAIN.bytes) \
    $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 24 128 32 $rate 8 2 4 heading-credited-every-level-pair > $E/parity77-$name.log 2>&1
  echo "PARITY77 $name rc=$? $(grep -E 'TOWER_PARITY_DONE|TOWER_PARITY_NEXT|MEASURE|rror' $E/parity77-$name.log | tr '\n' ' ')"
done
cd $W && PATH=/opt/cuda/bin:$PATH timeout 900 python3 -I $R/measure.py suite77 cargo test --release -p holonics-cuda --test tower_pass -- --include-ignored --test-threads=1 > $E/suite77.log 2>&1
echo "SUITE77 rc=$? $(grep -E 'test result|MEASURE|FAILED' $E/suite77.log | tr '\n' ' ')"
