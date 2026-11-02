#!/usr/bin/env bash
# Record §44's run-away read at a finer grain: the participating pair learner resumed from its lap-12
# state (STATE.11) for two laps with its lines read every 4 sections (TOWER_WINDOW_SECTIONS=4), so the
# carrier that grows first is seen. Projection 2 x 147.2 s = 294 s; deadline 340 s.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
US=d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
BIN=${BIN:-$R/bin/tower_pass-44a}
E=$R/race/g47; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
FROM=$R/race/g46/pa0/STATE.11
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR
export TOWER_PARTICIPATION_FROM=0 TOWER_PARTICIPATION_SECTION=256 TOWER_WINDOW_SECTIONS=4
echo "BIN=$(sha $BIN) FROM=$(sha $FROM) at=$(date -u +%FT%TZ)"
O=$E/pa0; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py pa0-fine timeout 340 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-participating-pair-unit-tower $U $US \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/DEV.roles $(sha $G/DEV.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 2 7 $O $FROM $(sha $FROM) > $O.log 2>&1
echo "RUN_END pa0-fine rc=$? $(grep -E 'TOWER_PASS |MEASURE|rror' $O.log | sed 's/train_code=[0-9]* dev_code=[0-9]* grain_bits=20//' | tr '\n' ' ')"
