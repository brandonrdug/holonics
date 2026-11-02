#!/usr/bin/env bash
# Acceptance 77's parity on the bytes at rate 2^(-5) (2^(-3) refused at section 3: the residual stream outgrew its
# 32-bit carrier), so that the card reads halved and refused steps against the host.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run; G=$R/gsm8k; E=$R/race/bytes-1101
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION TOWER_NEXT_SECTION
B77=$R/bin/tower_pass-77a; u=$G/UNITS0
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_NEXT_SECTION=1 \
  python3 -I $R/measure.py parity77-bytes5 timeout 300 $B77 parity-units-founded $u $(sha $u) $G/TRAIN.bytes $(sha $G/TRAIN.bytes) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 24 128 32 5 8 2 4 heading-credited-every-level-pair > $E/parity77-bytes5.log 2>&1
echo "PARITY77 bytes5 rc=$? $(grep -E 'TOWER_PARITY_DONE|TOWER_PARITY_NEXT|MEASURE|rror' $E/parity77-bytes5.log | tr '\n' ' ')"
