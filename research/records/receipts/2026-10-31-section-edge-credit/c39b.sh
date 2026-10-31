#!/usr/bin/env bash
# Record §39, acceptance 67 (second part), 160 streams from the founding: one lap of width 128 (737
# sections; projection 737 x 0.424 s, its largest measured per-section time over the development
# read's first 32 sections, = 312 s; deadline 360 s) and three laps of width 64 (its lap read 120.1 s,
# largest measured section 0.248 s: 3 x 737 x 0.248 = 548 s; deadline 600 s) so the width-128 lap's end
# lies between two of width 64's; then the flux on the continuation's opening for the width-128 lap and
# width 64's laps 2 and 3, and the width-128 lap's writing (agree 1 and 2).
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
K=$D/KEYS8; KS=01db1cf4ddc06e086951b8dad07b89661ed3238555eba598dccbbdba6817b6cf
BIN=${BIN:-$R/bin/tower_pass-36b}
E=$R/race/c39; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_PARTICIPATION_SECTION TOWER_LAP_SECTIONS
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
for run in "w128:128 128 512:1:360" "w64:64 128 256:3:600"; do
  name=${run%%:*}; rest=${run#*:}; shape=${rest%%:*}; rest=${rest#*:}; passes=${rest%%:*}; limit=${rest#*:}
  O=$E/lap-$name; rm -rf $O
  nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
  VRAM=$!
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py lap-$name timeout $limit $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-unit-tower \
    $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
    $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $K $KS $shape 6 160 128 $passes 7 $O > $O.log 2>&1
  echo "RUN_END lap-$name rc=$? $(grep -E 'TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
  kill $VRAM; echo "VRAM_PEAK_MIB $name=$(sort -n $O.vram | tail -1)"
done
export TOWER_END_CLASS=30
for pair in "w128:$E/lap-w128/STATE" "w64-lap2:$E/lap-w64/STATE.1" "w64-lap3:$E/lap-w64/STATE"; do
  name=${pair%%:*}; S=${pair#*:}
  [ -f "$S" ] || { echo "FLUX_$name absent"; continue; }
  rm -rf $E/flux-lap-$name
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py flux-lap-$name timeout 300 $BIN read complete-language read-tower-race \
    $S $(sha256sum $S | cut -c1-64) $D/DEV.units 435334a82c9ab4ff8e59213776c73f6754bd7a866419cdb4ec5eda8201da0583 \
    $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f 24 128 $E/flux-lap-$name > $E/flux-lap-$name.log 2>&1
  echo "FLUX_$name rc=$? $(grep -E 'TOWER_RACE_FLUX_HEAD prompt=[0-2] head=256|MEASURE|rror' $E/flux-lap-$name.log | tr '\n' ' ')"
done
S=$E/lap-w128/STATE
for a in 1 2; do
  rm -rf $E/release$a-w128
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py release$a-w128 timeout 120 $BIN release complete-language release-tower-classes \
    $S $(sha256sum $S | cut -c1-64) $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f \
    $ROOT/.local/wt/race/.local/race/passage/RELEASE_KEYS 9e358671eb6968c1f4b624611b41de7fed4ede5fc1af9532a8d9db36f3c9b739 1024 $a $E/release$a-w128 > $E/release$a-w128.log 2>&1
  echo "RELEASE_END $a w128 rc=$? $(grep -E 'CLASSES_RELEASE_CODE|MEASURE|rror' $E/release$a-w128.log | tr '\n' ' ')"
done
