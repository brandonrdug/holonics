#!/usr/bin/env bash
# Record §39, acceptances 66-67 (first part): the card against the host at the wider declaration on
# units (W 128, F 512), 24 streams over 32 sections (deadline 300 s; the width-64 parity ran 72 s and
# about twice the material), then the development read at 160 streams, 128 sections (projection: the
# width-64 read's 24.9 s times about three, 75 s; deadline 240 s), then its flux (300 s).
set -u
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
K=$D/KEYS8; KS=01db1cf4ddc06e086951b8dad07b89661ed3238555eba598dccbbdba6817b6cf
BIN=${BIN:-$R/bin/tower_pass-36b}
E=$R/race/c39; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_PARTICIPATION_SECTION
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity-w128 timeout 300 $BIN parity-units-founded \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a \
  $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $K $KS 128 128 512 6 24 128 32 7 8 2 4 heading-credited-every-level > $E/parity-w128.log 2>&1
echo "PARITY_W128 rc=$? $(grep -E 'TOWER_PARITY_DONE|MEASURE|rror' $E/parity-w128.log | tr '\n' ' ')"
grep -q 'gradient_unequal=0 learners_unequal=0' $E/parity-w128.log || { echo "PARITY_FAILED stop"; exit 0; }
export TOWER_LAP_SECTIONS=128
O=$E/dev160-w128; rm -rf $O
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
VRAM=$!
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py dev160-w128 timeout 240 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-unit-tower \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $K $KS 128 128 512 6 160 128 1 7 $O > $O.log 2>&1
echo "RUN_END dev160-w128 rc=$? $(grep -E 'TOWER_TRAIN|TOWER_SECTION|TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $O.vram | tail -1)"
S=$O/STATE
[ -f "$S" ] || { echo "FLUX absent"; exit 0; }
rm -rf $E/flux-w128
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
  python3 -I $R/measure.py flux-w128 timeout 300 $BIN read complete-language read-tower-race \
  $S $(sha256sum $S | cut -c1-64) $D/DEV.units 435334a82c9ab4ff8e59213776c73f6754bd7a866419cdb4ec5eda8201da0583 \
  $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f 24 128 $E/flux-w128 > $E/flux-w128.log 2>&1
echo "FLUX_w128 rc=$? $(grep -E 'TOWER_RACE_FLUX_HEAD|MEASURE|rror' $E/flux-w128.log | tr '\n' ' ')"
