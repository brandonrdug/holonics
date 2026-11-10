#!/bin/bash
# octave.sh STATE TAG: the keyed order given the held answers' lengths, split by octave (theory's reading, November 10 21:03; order-field of
# field_pass.octave, BUILD.octave: the v14 face line's reads binary, claude/v14-face-line, with FIELD_ORDER_OCTAVE lines added beside the
# unchanged FIELD_ORDER line). keyed_given_bits_a_letter's states exactly (the lane laps' order read, held 0-31, the lane_lap.sh environment
# with FIELD_CLOCK_BARE), its code summed by the octave of each place's position (octave j: positions d in [2^j, 2^(j+1)), d one-based),
# the mean code in nats and the places an octave; FIELD_ORDER_OCTAVE_NOTE says which places an octave locks and what is written when it does;
# FIELD_ORDER_OCTAVE_TOTAL is the whole read (ct6: 2.420 bits = 1.6775 nats a letter). Theory's G18, finest octave first: 0.90, 1.80, 2.70,
# 3.15, 3.30 nats; the text row (stride s locking odd multiples of s) 0.698, 1.654, 2.619, 3.2. A short card stage of its own (flock -w 14400
# on .local/gpu.lock), so it fits between laps. Output under $N/octave/TAG.*. Projection: a measured read of ct6, 55 s wall (the order read, 0.57 GB resident): 60 s, deadline 75 s.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass.octave; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || { echo "octave.sh STATE TAG"; exit 2; }
S=$1; TAG=$2; O=$N/octave
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
mkdir -p $O; rm -rf $O/$TAG
PROJ=60; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $N/BUILD.octave) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); projected $PROJ s, deadline $DEAD s"
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
( flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
  echo "# lock taken $(date -u +%H:%M:%S)"
  $M octave_$TAG timeout $DEAD $BIN train complete-language order-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 $O/$TAG > $O/$TAG.log 2>&1
) 9>$ROOT/.local/gpu.lock
grep -E '^FIELD_ORDER |^FIELD_ORDER_OCTAVE|^MEASURE|rror|panic|refused' $O/$TAG.log | sed -E 's/(FIELD_ORDER problems=[0-9]+ places=[0-9]+ ).*(keyed_given_bits_a_letter=[0-9.]+).*/\1... \2 .../' | cut -c1-330
echo "TRANSMISSION_OCTAVE $TAG G18(finest first) 0.90 1.80 2.70 3.15 3.30; text 0.698 1.654 2.619 3.2"
echo "MAIN octave exit $(date -u +%H:%M:%S)"
