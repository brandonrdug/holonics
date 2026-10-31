#!/usr/bin/env bash
# Record §38, acceptance 65: the development read with participation's section at 512 of its level's
# ticks, 128 sections of 160 streams from C′'s founding keys, then the flux on the continuation's
# opening (end letter unit 30). Projection 250 s (the 128-tick read's participation share times four
# beside the unit declaration's 24.9 s); deadline 400 s; the flux read 300 s (measured 41 s).
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
BIN=${BIN:-$R/bin/tower_pass-36b}
E=$R/race/u38; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL
export TOWER_LAP_SECTIONS=128 TOWER_PARTICIPATION_SECTION=512
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
O=$E/dev160-reach512; rm -rf $O
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
VRAM=$!
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py dev160-reach512 timeout 400 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-participating-unit-tower \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $ROOT/.local/wt/race/.local/race/passage/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 160 128 1 7 $O > $O.log 2>&1
echo "RUN_END dev160-reach512 rc=$? $(grep -E 'TOWER_PARTICIPATION|TOWER_SECTION|TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $O.vram | tail -1)"
export TOWER_END_CLASS=30
S=$O/STATE
[ -f "$S" ] || { echo "FLUX absent"; exit 0; }
rm -rf $E/flux-reach512
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py flux-reach512 timeout 300 $BIN read complete-language read-tower-race \
  $S $(sha256sum $S | cut -c1-64) $D/DEV.units 435334a82c9ab4ff8e59213776c73f6754bd7a866419cdb4ec5eda8201da0583 \
  $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f 24 128 $E/flux-reach512 > $E/flux-reach512.log 2>&1
echo "FLUX_reach512 rc=$? $(grep -E 'TOWER_RACE_FLUX_HEAD|MEASURE|rror' $E/flux-reach512.log | tr '\n' ' ')"
