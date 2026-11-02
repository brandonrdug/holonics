#!/usr/bin/env bash
# Record §41, acceptances 70-71: the card against the host for the working declaration with pair
# contacts on units (24 streams, 32 sections; deadline 300 s, the rectifying parity ran 72 s), then
# three laps at 160 streams from C′'s founding keys (projection: the rectifier's largest measured
# section 0.248 s times C′'s pair-to-rectifier pass ratio 1.5, 0.372 s x 2,211 sections = 823 s;
# deadline 900 s), then the flux after its third lap.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
BIN=${BIN:-$R/bin/tower_pass-41a}
E=$R/race/p41; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_PARTICIPATION_SECTION TOWER_LAP_SECTIONS
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity-pair timeout 300 $BIN parity-units-founded \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a \
  $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level-pair > $E/parity-pair.log 2>&1
echo "PARITY_PAIR rc=$? $(grep -E 'TOWER_PARITY_DONE|MEASURE|rror' $E/parity-pair.log | tr '\n' ' ')"
grep -q 'gradient_unequal=0 learners_unequal=0' $E/parity-pair.log || { echo "PARITY_FAILED stop"; exit 0; }
O=$E/lap-pair; rm -rf $O
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
VRAM=$!
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py lap-pair timeout 900 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-pair-unit-tower \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $D/DEV.bytes f8a708865f61cb3df771e70b8c18b692d4c9a124b1c15cba5be68c79c21762b4 $D/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 160 128 3 7 $O > $O.log 2>&1
echo "RUN_END lap-pair rc=$? $(grep -E 'TOWER_SECTION pass=0 section=(32|64) |TOWER_PASS |TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ')"
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $O.vram | tail -1)"
S=$O/STATE
[ -f "$S" ] || { echo "FLUX absent"; exit 0; }
rm -rf $E/flux-pair
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
  python3 -I $R/measure.py flux-pair timeout 300 $BIN read complete-language read-tower-race \
  $S $(sha256sum $S | cut -c1-64) $D/DEV.units 435334a82c9ab4ff8e59213776c73f6754bd7a866419cdb4ec5eda8201da0583 \
  $D/PROMPTS.units 8d7c42f15dbc0eaa03990e568e04e05f053ee0fe383b1f9ab690d70a8107450f 24 128 $E/flux-pair > $E/flux-pair.log 2>&1
echo "FLUX_pair rc=$? $(grep -E 'TOWER_RACE_FLUX_HEAD prompt=[0-2] head=256|MEASURE|rror' $E/flux-pair.log | tr '\n' ' ')"
