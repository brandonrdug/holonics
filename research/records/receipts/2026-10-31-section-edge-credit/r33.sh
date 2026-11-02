#!/usr/bin/env bash
# Record §33, acceptance 60: the unit declaration for two laps from C′'s founding (its lap is the
# passage's 368 sections of units). Projection from the development read's 0.386 s a section (its
# first window's refusals make it the upper rate): 142 s a lap, two laps with their held-out reads and
# close about 300 s; deadline 360 s. Then its writing from the second lap's learner (agree 1 and 2,
# the prompts parsed in the same units, the end letter's class the record separator's unit 30;
# deadline 90 s each), decoded at the boundary.
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
BIN=$R/bin/tower_pass-33c
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_LAP_SECTIONS TOWER_FACE_GLOBAL
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $D/vram-race.log &
VRAM=$!
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
O=$D/race; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py unit-race timeout 360 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-unit-tower \
  $U $(sha256sum $U | cut -c1-64) $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $ROOT/.local/wt/race/.local/race/passage/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 320 128 2 7 $O > $O.log 2>&1
echo "RUN_END unit-race rc=$? $(grep -E 'TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
S=$O/STATE.1
export TOWER_END_CLASS=30
for a in 1 2; do
  rm -rf $D/release$a
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
    python3 -I $R/measure.py release$a timeout 90 $BIN release complete-language release-tower-classes \
    $S $(sha256sum $S | cut -c1-64) $D/PROMPTS.units $(sha256sum $D/PROMPTS.units | cut -c1-64) \
    $ROOT/.local/wt/race/.local/race/passage/RELEASE_KEYS 9e358671eb6968c1f4b624611b41de7fed4ede5fc1af9532a8d9db36f3c9b739 1024 $a $D/release$a > $D/release$a.log 2>&1
  echo "RELEASE_END $a rc=$? $(grep -E 'CLASSES_RELEASE_CODE|CLASSES_RELEASE_DONE|MEASURE|rror' $D/release$a.log | tr '\n' ' ')"
done
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $D/vram-race.log | tail -1)"
