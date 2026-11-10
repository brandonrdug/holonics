#!/bin/bash
# ringtilt.sh STATE TAG RINGDIR [PROBLEMS] [START]: the ring tilts in the certificate (theory, November 10 04:40; claude/exchange-walk,
# the commit in BUILD.ringtilt), with long114's laws, every output under $O/TAG/: redraw-ring-field, redraw.sh's walk (point
# re-draws at the highest surprise alternating with exchanges, h = 1 nat, the same start and the same stops) with every face it reads
# tilted by the spread ring census in RINGDIR (RING.tsv and RING_STOP.tsv from `ring.sh STATE TAG every-6`): ln(N/F) per (ring,
# residue, letter) pooled over TRAIN's two sets, a cell under 2,000 sites dropped; each place's face at the ring residues of its
# answer's letters before it, the stop place (coded at the void) at the whole answer's. FIELD_REDRAW_PASS each pass as the re-draw
# prints it; FIELD_RING_CLOSURE the near and far bracket closure and the quotes' parity at the start and the end; FIELD_REDRAW at
# each stop. PROBLEMS defaults to 32 and START to lap 26's parallel rest (settle26/settle/SAMPLE.tsv); for another count with no
# START, give the start redraw.sh settled (its TAG/settle/SAMPLE.tsv). Every pass saved, private. The defect bound 1,000 passes.
# Projection: the settle's measured largest pass at lap 26 (27.6 s for 32 problems) scaled by the problems, times the bound, and
# 60 s; deadline 1.25 x (a guard). RTX 4080 SUPER under .local/gpu.lock (flock -w 14400).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-09-exchange; BIN=$O/field_pass.ringtilt; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -ge 3 ] && [ $# -le 5 ] || { echo "ringtilt.sh STATE TAG RINGDIR [PROBLEMS] [START]"; exit 2; }
S=$1; TAG=$2; RD=$3; N=${4:-32}; START=${5:-}
[ -z "$START" ] && [ "$N" -eq 32 ] && START=$O/settle26/settle/SAMPLE.tsv
[ -n "$START" ] && [ -f "$START" ] || { echo "MAIN no start: give START (for $N problems, redraw.sh's TAG/settle/SAMPLE.tsv)"; exit 1; }
RING=$RD/RING.tsv; STOP=$RD/RING_STOP.tsv; FLOOR=2000
[ -f $RING ] && [ -f $STOP ] || { echo "MAIN no ring census tables in $RD"; exit 1; }
OUT=$O/$TAG; mkdir -p $OUT
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
BOUND=1000; APASS=$(( 27600 * N / 32 )); PROJ=$(( BOUND * APASS / 1000 + 60 )); DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $O/BUILD.ringtilt 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); $N problems from $(sha $START); ring $(sha $RING) stop $(sha $STOP) floor $FLOOR; projected $PROJ s, deadline $DEAD s"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the walk reads it on the declared bare clock";; esac
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
rm -rf $OUT/ringtilt
$M ringtilt timeout $DEAD $BIN train complete-language redraw-ring-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $N $START $(sha $START) 1000 $BOUND $RING $(sha $RING) $STOP $(sha $STOP) $FLOOR $OUT/ringtilt > $OUT/ringtilt.log 2>&1
grep -E '^FIELD_RING_TILTS|^FIELD_REDRAW_DONE|^FIELD_RING_CLOSURE|^MEASURE|rror|panic|refused' $OUT/ringtilt.log | cut -c1-320
echo "== each pass"
grep -E '^FIELD_REDRAW_PASS' $OUT/ringtilt.log | cut -c1-300
echo "== each problem at its stop"
grep -E '^FIELD_REDRAW ' $OUT/ringtilt.log | cut -c1-240
D=$(grep -cE '^FIELD_REDRAW .* stop=bound' $OUT/ringtilt.log); [ "$D" -eq 0 ] || echo "# DEFECT: $D problems stopped by the $BOUND-pass defect bound"
echo "MAIN exit $(date -u +%H:%M:%S)"
