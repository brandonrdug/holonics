#!/usr/bin/env bash
# The coordinator's profile (November 1): 32 sections of R1's and of R2's declaration on the bytes, alternated, alone
# under the card's lock: first each with TOWER_PROFILE (every launch timed alone, the card synchronized around it),
# then each unprofiled with the card's utilization sampled every 100 ms (sm = time a kernel ran, memory = time
# the memory was read or written), and the host's share from TOWER_CARD. Each run is one lap of 32 sections
# (TOWER_LAP_SECTIONS=32) and its held-out read; deadline 180 s each.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run; G=$R/gsm8k; E=$R/race/bytes-1101/prof; mkdir -p $E
BIN=$R/bin/tower_pass-46a; U=$G/UNITS0
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION TOWER_NEXT_SECTION
R1=train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower
R2=train-two-ladder-stacked-news-heading-credited-every-level-participating-pair-unit-tower
run() { # name route profile env...
  local name=$1 route=$2 prof=$3; shift 3
  local O=$E/$name; rm -rf $O
  nvidia-smi --query-gpu=timestamp,utilization.gpu,utilization.memory,memory.used,clocks.sm --format=csv,noheader,nounits -lms 100 > $O.util &
  local SMI=$!
  local envs=(-E TOWER_LAP_SECTIONS=32 -E TOWER_WINDOW_SECTIONS=8 "$@"); [ $prof = 1 ] && envs+=(-E TOWER_PROFILE=1)
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 "${envs[@]}" \
    python3 -I $R/measure.py $name timeout 180 $BIN train complete-language $route $U $(sha $U) \
    $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/COPY.roles $(sha $G/COPY.roles) \
    $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 1 8 $O > $O.log 2>&1
  local rc=$?; kill $SMI
  echo "PROF $name rc=$rc $(grep -E 'TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
}
run r1-prof $R1 1
run r2-prof $R2 1 -E TOWER_PARTICIPATION_FROM=4 -E TOWER_PARTICIPATION_SECTION=128
run r1-plain $R1 0
run r2-plain $R2 0 -E TOWER_PARTICIPATION_FROM=4 -E TOWER_PARTICIPATION_SECTION=128
