#!/bin/bash
# refread.sh STATE TAG: the references' locked code and summed entropy on all of HELD128 (theory, November 10 09:55): each held
# reference answer read with every place locked (every face once, that place alone open), exactly as charge.sh reads its
# "reference" state, on all 128 problems and for the reference alone (FIELD_CHARGE_REFERENCE_ONLY: charge-field skips the settle's
# rest and keyed write). Printed: code and entropy a place (nats), the share of places with v > 1 and v > 2, and the root charge.
# Run for both arms each lap (the control's states are in the lane chain's lap directories). The clock is charge.sh's (FIELD_CLOCK_BARE,
# the census's declared reading). Outputs under $N/refread/TAG. One binary (the build in BUILD) reads both arms.
# Projection (PROJECTION.txt): measured 114.4 s (lap33's state) and 116.0 s (its growth) wall; 120 s, deadline 150 s. RTX 4080 SUPER under .local/gpu.lock.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || { echo "refread.sh STATE TAG"; exit 2; }
S=$1; TAG=$2
O=$N/refread/$TAG
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
PROJ=120; DEAD=$(( PROJ * 5 / 4 ))
mkdir -p $N/refread
echo "# BUILD $(cat $N/BUILD) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); projected $PROJ s, deadline $DEAD s"
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1 FIELD_CHARGE_REFERENCE_ONLY=1
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
rm -rf $O
$M refread_$TAG timeout $DEAD $BIN train complete-language charge-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 128 - - - - $O > $N/refread/$TAG.log 2>&1
grep -E '^FIELD_CHARGE_STATE|^FIELD_CHARGE_DONE|^MEASURE|rror|panic|refused' $N/refread/$TAG.log | cut -c1-320
L=$(grep -E '^FIELD_CHARGE_STATE state=reference ' $N/refread/$TAG.log | sed -E 's/.*problems=([0-9]+) letters=([0-9]+).*code_nats_a_place=([0-9.]+) entropy_nats_a_place=([0-9.]+).*root_share_of_excess=([0-9.-]+) v_over_1_share=([0-9.]+) v_over_2_share=([0-9.]+).*/problems=\1 places=\2 code=\3 entropy=\4 root_share=\5 v1=\6 v2=\7/')
echo "REFREAD $TAG ${L:-none} $(date -u +%H:%M:%S)"
