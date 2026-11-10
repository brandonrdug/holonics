#!/bin/bash
# grow.sh FROM OUT: grow the contacts of the lane state FROM (D 64 in 2 lanes, f 32) by 32 pair contacts (f 64) into OUT/STATE.0
# (theory's order, November 10 09:55; claude/exchange-walk, the commit in BUILD). The new contacts' drives are drawn as a founding
# draws them (uniform on +-sqrt(3/D) at the material's grain) from the key file past every draw the state has read; W's new columns
# and the contacts' biases open at zero, so every sum the forward forms is the old sum. grow-contacts-field reads the held joint
# (HELD128's own and foil states, 128 problems) before (lap=-1) and after (lap=0) the growth on the card, with the lap's own clock
# (no FIELD_CLOCK_BARE: lane2.sh's law, as lane_lap.sh trains), compares the FACES of every one of those states bit for bit and
# REFUSES to write the grown state where one moved; this script then checks the two FIELD_JOINT_NATS agree and that the grown
# state's own head says f 64. The binary is field_pass.v14 (BUILD.v14): the lane chain's training line (01bd3b362, v14, no carried remainders; train-field on
# lane33's state reproduces lap34's 227 first sections bit for bit) with the growth of 6036ed848 ported; the grown state is a v14 state the lane chain's own binaries read. The grown state resumes under contacts_lap.sh with train-field's arguments unchanged.
# Projection (measured, see PROJECTION below): the card lock, one load of the state, four joint reads of 128 problems; deadline
# 1.25 x the projection. RTX 4080 SUPER under .local/gpu.lock (flock -w 14400).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass.v14; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
LOCK=$ROOT/.local/gpu.lock
ADDED=32
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || { echo "grow.sh FROM OUT"; exit 2; }
FROM=$1; OUT=$2
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
[ -e $OUT/STATE.0 ] && { echo "MAIN $OUT/STATE.0 exists: not overwritten"; exit 1; }
mkdir -p $OUT
# Projection (PROJECTION.txt): the measured grow of lap33/STATE.0 took 9.4 s on the card (12 s with the lock and hashes); 20 s, deadline 25 s.
PROJ=20; DEAD=$(( PROJ * 5 / 4 ))
echo "# grow $(sha $FROM): $(sed -n 2p $FROM | cut -c1-60) + $ADDED contacts; binary $(sha $BIN) build $(head -c 120 $N/BUILD.v14); projected $PROJ s, deadline $DEAD s $(date -u +%H:%M:%S)"
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1
unset FIELD_CLOCK_BARE
exec 9>$LOCK; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
$M grow timeout $DEAD $BIN train complete-language grow-contacts-field $FROM $(sha $FROM) $K $(sha $K) $ADDED $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $OUT/STATE.0 > $OUT/grow.log 2>&1
grep -E '^FIELD_GROW|^FIELD_JOINT_NATS|^FIELD_GROWN|^MEASURE|rror|panic|refused|moved a face' $OUT/grow.log | cut -c1-260
[ -f $OUT/STATE.0 ] || { echo "MAIN the growth wrote no state"; exit 1; }
J0=$(grep -E '^FIELD_JOINT_NATS lap=-1 ' $OUT/grow.log | sed -E 's/.*own_nats_a_place=([0-9.]+).*/\1/')
J1=$(grep -E '^FIELD_JOINT_NATS lap=0 ' $OUT/grow.log | sed -E 's/.*own_nats_a_place=([0-9.]+).*/\1/')
KEPT=$(grep -cE '^FIELD_GROW_CONTACTS_KEPT .* identical=true' $OUT/grow.log)
HEAD=$(sed -n 2p $OUT/STATE.0 | cut -d' ' -f1-12)
echo "# the grown state $(sha $OUT/STATE.0): $HEAD"
if [ "$KEPT" = 1 ] && [ -n "$J0" ] && [ "$J0" = "$J1" ] && [ "$(sed -n 2p $OUT/STATE.0 | cut -d' ' -f7)" = $(( $(sed -n 2p $FROM | cut -d' ' -f7) + ADDED )) ]; then
  echo "GROW ok: every face of HELD128's joint states kept bit for bit; the plain held joint $J0 -> $J1 nats a place"
else
  echo "MAIN GROW FAILED: faces kept=$KEPT, held joint $J0 -> $J1 (the grown state is not to be trained)"; mv $OUT/STATE.0 $OUT/STATE.0.refused; exit 1
fi
echo "MAIN exit $(date -u +%H:%M:%S)"
