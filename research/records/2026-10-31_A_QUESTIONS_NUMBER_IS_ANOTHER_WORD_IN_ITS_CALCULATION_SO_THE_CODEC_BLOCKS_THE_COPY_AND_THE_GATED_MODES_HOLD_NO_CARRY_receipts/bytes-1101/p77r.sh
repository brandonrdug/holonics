#!/usr/bin/env bash
# (A)'s card parity: the working declaration on the committed units at 2^(-8), the next-section law declared, both
# learners read back from their text after section 16 (TOWER_PARITY_RESTORE=16), 32 sections; deadline 300 s.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run; G=$R/gsm8k; E=$R/race/bytes-1101
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION
B=$R/bin/tower_pass-77b
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_NEXT_SECTION=1 -E TOWER_PARITY_RESTORE=16 \
  python3 -I $R/measure.py parity77-restore timeout 300 $B parity-units-founded $U $(sha $U) $G/TRAIN.bytes $(sha $G/TRAIN.bytes) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 24 128 32 8 8 2 4 heading-credited-every-level-pair > $E/parity77-restore.log 2>&1
echo "PARITY77R rc=$? B=$(sha $B) $(grep -E 'TOWER_PARITY_RESTORE|TOWER_PARITY_DONE|TOWER_PARITY_NEXT|MEASURE|rror' $E/parity77-restore.log | tr '\n' ' ')"
