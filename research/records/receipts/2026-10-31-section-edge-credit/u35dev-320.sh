#!/usr/bin/env bash
# Record §35, acceptance 62: the development read on units with participation at the clocked levels,
# its first 64 sections from C′'s founding keys beside §33's (28.8 s), then the flux on the
# continuation's opening for both learners and for the unit declaration's lap-1 learner (acceptance 63's
# baseline) (read-tower-race on DEV.units and PROMPTS.units, 24
# streams of 128). Unmeasured: the read planned at three minutes (deadline 180 s); each flux read's
# deadline 300 s (the participating byte flux read ran 259.6 s, the plain 66.4 s).
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
BIN=${BIN:-$R/bin/tower_pass-35d}
E=$R/race/u35; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL
export TOWER_LAP_SECTIONS=64
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
O=$E/dev; rm -rf $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py unit-dev-participating timeout 180 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-participating-unit-tower \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $ROOT/.local/wt/race/.local/race/passage/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 320 128 1 7 $O > $O.log 2>&1
echo "RUN_END unit-dev-participating rc=$? $(grep -E 'TOWER_PARTICIPATION|TOWER_SECTION|TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
for pair in "participating:$O/STATE" "plain:$D/dev/STATE" "lap1-plain:$D/race/STATE.0"; do
  name=${pair%%:*}; S=${pair#*:}
  [ -f "$S" ] || { echo "FLUX_$name absent"; continue; }
  rm -rf $E/flux-$name
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py flux-$name timeout 300 $BIN read complete-language read-tower-race \
    $S $(sha256sum $S | cut -c1-64) $D/DEV.units 435334a82c9ab4ff8e59213776c73f6754bd7a866419cdb4ec5eda8201da0583 \
    $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f 24 128 $E/flux-$name > $E/flux-$name.log 2>&1
  echo "FLUX_$name rc=$? $(grep -E 'TOWER_RACE_FLUX|MEASURE|rror' $E/flux-$name.log | tr '\n' ' ')"
done
