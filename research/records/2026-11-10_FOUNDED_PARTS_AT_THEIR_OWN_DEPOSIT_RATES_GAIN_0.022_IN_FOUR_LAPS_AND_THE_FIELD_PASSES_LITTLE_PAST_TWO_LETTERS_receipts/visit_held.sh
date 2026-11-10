#!/bin/bash
# visit_held.sh STATE TAG (theory, November 10 19:40: HELD128 only, the same layout): the locked visit's records (theory's order 2, November 10; locked-visit-field, the commit in BUILD.visit) of STATE on
# HELD128 and TRAIN's parity samples (every-6, as the reach census read them): for each answer place of each reference (cut to its room,
# every place read once with the rest locked, and the stop place where the room holds it) one packed binary record, in problem then place
# order, to $N/visit/TAG/{held,train_even,train_odd}.bin with a .header each (layout, alphabet, width, record count, the state's sha,
# the grains: shares u16 at 2^-16 released by partition with the remainder dropped; the readout chart i32 on its own 2^-16 grain).
# Numbers only: no passage text is written; the files stay under .local.
# Each set is a card stage of its own (flock -w 14400 on .local/gpu.lock), so the arms' stages interleave; a set whose .bin exists is not
# read again. Clocks: the census's declared reading (FIELD_CLOCK_BARE), as charge.sh and refread.sh.
# Projection (measured November 10 on lap33/STATE.0, HELD128 alone, 128 problems, 43,470 records, 127.8 s of the read, 128.2 s wall, peak
# 0.94 GB resident): 2.94 ms a record on the card. TRAIN's samples: 675,553 and 668,383 letter places (the reach census's counts) plus one
# stop a problem (2,058 and 2,057): 677,611 and 670,440 records, at 2.94 ms 1,992 s and 1,971 s, and 60 s to load: 2,052 s each,
# deadline 1.25 x = 2,565 s (a guard: the run stops at its deadline, its set incomplete, and is not relaunched larger). HELD128: 140 s,
# deadline 175 s. Record 467 bytes (alphabet 100, width 64): HELD128 20.3 MB, train_even 316.4 MB, train_odd 313.1 MB, 649.8 MB in all.
# The host holds one batch of 32 problems and 256 regions' charts at a time. RTX 4080 SUPER under .local/gpu.lock.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass.visit; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
LOCK=$ROOT/.local/gpu.lock
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || { echo "visit.sh STATE TAG"; exit 2; }
S=$1; TAG=$2; O=$N/visit/$TAG
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
mkdir -p $O
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
echo "# BUILD $(cat $N/BUILD.visit) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60) $(date -u +%H:%M:%S)"
for set in held; do
  [ -e $N/STOP ] && { echo "MAIN STOP read: the visit stops before $set"; exit 0; }
  [ -e $O/$set.header ] && { echo "# $set already read"; continue; }
  case $set in held) PROJ=140;; *) PROJ=2052;; esac; DEAD=$(( PROJ * 5 / 4 ))
  rm -f $O/$set.bin
  ( flock -w 14400 9 || { echo "MAIN LOCK_BUSY at $set"; exit 75; }
    echo "# $set: lock taken $(date -u +%H:%M:%S); projected $PROJ s, deadline $DEAD s"
    $M visit_${TAG}_$set timeout $DEAD $BIN train complete-language locked-visit-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) every-6 $set $O > $O/$set.log 2>&1
  ) 9>$LOCK
  grep -E '^FIELD_VISIT_SET|^MEASURE|rror|panic|refused' $O/$set.log | cut -c1-250
  [ -e $O/$set.header ] || { echo "MAIN $set left no header (stopped or failed)"; exit 1; }
done
echo "MAIN visit exit $(date -u +%H:%M:%S)"
