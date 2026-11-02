#!/usr/bin/env bash
# Record §35, acceptance 63, at 160 streams (§36): one lap each on units from C′'s founding keys, the
# unit declaration and the participating one; then the flux on the continuation's opening for both lap
# learners and the writing (class release, agree 1 and 2, the end letter unit 30) from both.
# Projection from the 128-section development reads (largest per-section time of each, its first 32
# sections with the run's opening): plain 737 x 0.248 s = 183 s (deadline 240 s); participating
# 737 x 0.813 s = 599 s (deadline 660 s, the lap's close and save beside it). Flux reads 300 s each
# (measured 27-42 s); releases 120 s each (measured 10-13 s; participation reads its sites on the host).
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
BIN=${BIN:-$R/bin/tower_pass-35d}
E=$R/race/r35; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
for run in "participating:train-two-ladder-stacked-news-heading-credited-every-level-participating-unit-tower:660" "plain:train-two-ladder-stacked-news-heading-credited-every-level-unit-tower:240"; do
  name=${run%%:*}; rest=${run#*:}; route=${rest%%:*}; limit=${rest#*:}
  O=$E/lap-$name; rm -rf $O
  nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
  VRAM=$!
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py lap-$name timeout $limit $BIN train complete-language $route \
    $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
    $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $ROOT/.local/wt/race/.local/race/passage/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 160 128 1 7 $O > $O.log 2>&1
  echo "RUN_END lap-$name rc=$? $(grep -E 'TOWER_SECTION pass=0 section=(128|256|384|512|640|736) |TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
  kill $VRAM; echo "VRAM_PEAK_MIB $name=$(sort -n $O.vram | tail -1)"
done
export TOWER_END_CLASS=30
for name in participating plain; do
  S=$E/lap-$name/STATE
  [ -f "$S" ] || { echo "AFTER_$name absent"; continue; }
  rm -rf $E/flux-$name
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py flux-$name timeout 300 $BIN read complete-language read-tower-race \
    $S $(sha256sum $S | cut -c1-64) $D/DEV.units 435334a82c9ab4ff8e59213776c73f6754bd7a866419cdb4ec5eda8201da0583 \
    $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f 24 128 $E/flux-$name > $E/flux-$name.log 2>&1
  echo "FLUX_$name rc=$? $(grep -E 'TOWER_RACE_FLUX_HEAD|MEASURE|rror' $E/flux-$name.log | tr '\n' ' ')"
  for a in 1 2; do
    rm -rf $E/release$a-$name
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
      python3 -I $R/measure.py release$a-$name timeout 120 $BIN release complete-language release-tower-classes \
      $S $(sha256sum $S | cut -c1-64) $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f \
      $ROOT/.local/wt/race/.local/race/passage/RELEASE_KEYS 9e358671eb6968c1f4b624611b41de7fed4ede5fc1af9532a8d9db36f3c9b739 1024 $a $E/release$a-$name > $E/release$a-$name.log 2>&1
    echo "RELEASE_END $a $name rc=$? $(grep -E 'CLASSES_RELEASE_CODE|MEASURE|rror' $E/release$a-$name.log | tr '\n' ' ')"
  done
done
