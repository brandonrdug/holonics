#!/bin/bash
# redraw.sh STATE TAG [PROBLEMS] [START]: point re-draws at the highest surprise, alternating with exchanges (theory, November 10
# 04:15 and 04:40; claude/exchange-walk, the commit in BUILD.redraw), with long114's laws, every output under $O/TAG/:
# redraw-field on the first PROBLEMS held problems (default 32), h = 1 nat, from START, a locked-state SAMPLE.tsv. With no START:
# for 32 problems the parallel settle's rest at lap 26 (settle26/settle/SAMPLE.tsv); for any other count the keyed locks given
# held's lengths and then a parallel exchange to rest (settle-field with field_pass.settle), run here first. Odd passes re-draw
# (places with v > 1 nat, the most first, claims of +-5 disjoint, each to its face's top letter given the rest where its bare
# price is at least a nat); even passes exchange as settle-field does; each pass kept on its claims' falls (> h) and certified
# whole. An answer stops only at neutrality (code <= its faces' summed entropy) or where nothing stands in a re-draw pass and an
# exchange pass in a row; the pass bound, 1,000, is a defect bound that does not bind on its own: a problem it stops is reported
# as a DEFECT. Every pass is saved (SAMPLE.pass<k>.tsv) beside SAMPLE.tsv, private.
# Projection: the settle's measured largest pass at lap 26 (27.6 s for 32 problems) scaled by the problems, times the defect
# bound, and 60 s to load, for the settle stage and for the re-draws alike; each deadline 1.25 x its projection. RTX 4080 SUPER
# under .local/gpu.lock (flock -w 14400).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-09-exchange; BIN=$O/field_pass.redraw; SETTLE=$O/field_pass.settle; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; E32=$R/2026-11-06-long114/HELD_ENDS.tsv
[ $# -ge 2 ] && [ $# -le 4 ] || { echo "redraw.sh STATE TAG [PROBLEMS] [START]"; exit 2; }
S=$1; TAG=$2; N=${3:-32}; START=${4:-}
[ -z "$START" ] && [ "$N" -eq 32 ] && START=$O/settle26/settle/SAMPLE.tsv
OUT=$O/$TAG; mkdir -p $OUT
[ -x $BIN ] || { echo "MAIN no binary at $BIN (or its parity has not passed)"; exit 1; }
BOUND=1000; APASS=$(( 27600 * N / 32 ))
PROJ=$(( BOUND * APASS / 1000 + 60 )); DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $O/BUILD.redraw 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); $N problems, start ${START:-the keyed locks settled here}"
echo "# the measured pass scaled to $N problems: $APASS ms; the defect bound $BOUND passes: projected $PROJ s, deadline $DEAD s a stage"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the walk reads it on the declared bare clock";; esac
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
if [ -z "$START" ]; then
  # The keyed locks given held's lengths, then a parallel exchange to rest.
  [ -x $SETTLE ] || { echo "MAIN no settle binary at $SETTLE"; exit 1; }
  ENDS=$OUT/HELD_ENDS.tsv
  python3 -I $O/held_ends.py $P/HELD128.txt $N $ENDS || { echo "MAIN the held lengths could not be written"; exit 1; }
  cmp -s <(head -33 $ENDS) $E32 || { echo "MAIN the held lengths' first 32 differ from long114's HELD_ENDS.tsv"; exit 1; }
  rm -rf $OUT/settle
  FIELD_WRITER_LENGTHS=$ENDS FIELD_WRITER_RUN_BITS=1 $M settle timeout $DEAD $SETTLE train complete-language settle-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $N 2062 1000 $BOUND $OUT/settle > $OUT/settle.log 2>&1
  echo "== the keyed locks settled to rest ($N problems)"
  grep -E '^FIELD_SETTLE_DONE|^MEASURE|rror|panic|refused' $OUT/settle.log | cut -c1-320
  grep -qE '^FIELD_SETTLE_DONE' $OUT/settle.log || { echo "MAIN the settle stage did not finish"; exit 1; }
  SD=$(grep -cE '^FIELD_SETTLE .* at_rest=false' $OUT/settle.log); [ "$SD" -eq 0 ] || echo "# DEFECT: $SD problems did not rest in the settle stage within $BOUND passes"
  START=$OUT/settle/SAMPLE.tsv
fi
[ -f $START ] || { echo "MAIN no start at $START"; exit 1; }
echo "# start $(sha $START)"
rm -rf $OUT/redraw
$M redraw timeout $DEAD $BIN train complete-language redraw-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $N $START $(sha $START) 1000 $BOUND $OUT/redraw > $OUT/redraw.log 2>&1
grep -E '^FIELD_REDRAW_DONE|^MEASURE|rror|panic|refused' $OUT/redraw.log | cut -c1-320
echo "== each pass"
grep -E '^FIELD_REDRAW_PASS' $OUT/redraw.log | cut -c1-300
echo "== each problem at its stop"
grep -E '^FIELD_REDRAW ' $OUT/redraw.log | cut -c1-240
D=$(grep -cE '^FIELD_REDRAW .* stop=bound' $OUT/redraw.log); [ "$D" -eq 0 ] || echo "# DEFECT: $D problems stopped by the $BOUND-pass defect bound, neither neutral nor at rest"
echo "MAIN exit $(date -u +%H:%M:%S)"
