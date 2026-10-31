#!/usr/bin/env bash
# Record §33's development read: the working declaration read in the October 23 founded units (1,318:
# the bytes and 1,062 founded on GSM8K), its first 64 sections from C′'s founding keys; the passage's
# end letter written as the record separator 0x1E, which the passage does not hold (agent-inferred, the
# boundary codec). An unmeasured run: deadline 180 s.
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
BIN=$R/bin/tower_pass-33c
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS
export TOWER_LAP_SECTIONS=64
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $D/vram.log &
VRAM=$!
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
# The wide alphabet's path read against the host at the race's declaration (the face kept in the
# frame, TOWER_FACE_GLOBAL; deadline 300 s, the every-level parity ran 28.5 s) and the card suite
# (deadline 300 s), before the development read.
P=$ROOT/.local/wt/race/.local/race/passage
TOWER_FACE_GLOBAL=1 systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_FACE_GLOBAL=1 \
  python3 -I $R/measure.py parity-face timeout 300 $BIN parity \
  $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level > $D/parity-face.log 2>&1
echo "PARITY_FACE rc=$? $(grep -E 'TOWER_PARITY_DONE|MEASURE|rror' $D/parity-face.log | tr '\n' ' ')"
cd $ROOT/.local/wt/section-edge
python3 -I $R/measure.py suite timeout 300 cargo test -p holonics-cuda --test tower_pass -- --include-ignored --test-threads=1 > $D/suite.log 2>&1
echo "SUITE rc=$? $(grep -E 'test result|MEASURE' $D/suite.log | tr '\n' ' ')"
O=$D/dev; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py unit-dev timeout 180 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-unit-tower \
  $U $(sha256sum $U | cut -c1-64) $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $ROOT/.local/wt/race/.local/race/passage/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 320 128 1 7 $O > $O.log 2>&1
echo "RUN_END unit-dev rc=$? $(grep -E 'UNIT_READ|TOWER_TRAIN|TOWER_SECTION|TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $D/vram.log | tail -1)"
