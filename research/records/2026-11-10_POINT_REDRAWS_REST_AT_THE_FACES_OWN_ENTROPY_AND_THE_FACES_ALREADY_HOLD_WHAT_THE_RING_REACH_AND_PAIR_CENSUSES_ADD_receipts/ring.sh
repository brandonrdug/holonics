#!/bin/bash
# ring.sh STATE TAG [SAMPLE]: the locked-state ring census (theory, November 10 02:03; claude/exchange-walk, the commit in BUILD.ring), with
# long114's laws, every output under $O/TAG/. ring-census-field: three sets, HELD128 and TRAIN's first 2,048 problems of each parity of
# their index; each reference (cut to its room) read with every place locked, every face once with that place alone open (the
# run from the references' re-read) and the stop place (the first void past the letters) likewise. On the host, from the
# reference's letters before each place, five ring residues: backticks mod 2, ( less ) mod 3, [ less ] mod 3, double quotes
# mod 2, single quotes mod 2. RING.tsv holds N and F by set, ring, residue and letter at the letters' places, RING_STOP.tsv the
# same at the stop places (F each share on the face's width 2^-62, its remainder carried on 2^-94). Numbers only: no text is
# printed or written; the references stay under .local.
# Projection: the run from the references' re-read at the measured 15 s for 32 problems' places: 4,224 problems in 132 batches,
# 1,980 s, and 60 s to load: 2,040 s; deadline 1.25 x, 2,550 s. One FIELD_RING_BATCH line a batch of 32. RTX 4080 SUPER under
# .local/gpu.lock (flock -w 14400).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-09-census2; BIN=$O/field_pass.ring; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || [ $# -eq 3 ] || { echo "ring.sh STATE TAG [SAMPLE]"; exit 2; }
SAMPLE=${3:-2048}  # TRAIN's sample of each parity: the first 2,048 (as first run), or every-6 (every 6th across the file, theory 03:45)
S=$1; TAG=$2
O=$O/$TAG; mkdir -p $O
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
PROJ=2040; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $(dirname $BIN)/BUILD.ring 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); projected $PROJ s, deadline $DEAD s"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the census reads it on the declared bare clock";; esac
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
rm -rf $O/ring
$M ring timeout $DEAD $BIN train complete-language ring-census-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) $SAMPLE $O/ring > $O/ring.log 2>&1
grep -E '^FIELD_RING_SET|^FIELD_RING_DONE|^MEASURE|rror|panic|refused' $O/ring.log | cut -c1-240
grep -E '^FIELD_RING_BATCH' $O/ring.log | awk 'NR % 16 == 1' | cut -c1-200; grep -E '^FIELD_RING_BATCH' $O/ring.log | tail -1 | cut -c1-200
ls -la $O/ring/
echo "MAIN exit $(date -u +%H:%M:%S)"
