#!/bin/bash
# lane_lap.sh FROM NAME: one lap of the lane field and its reads (theory's item 7, November 10 04:40), every output under
# $O/NAME*. The STOP file in this directory halts the lap before it starts. Each stage takes the card lock on its own
# (flock -w 14400 on .local/gpu.lock), so an ordered read can slot in between.
# 1. The lap: train-field from FROM for one lap under lane2.sh's law (the training env without FIELD_CLOCK_BARE, long114's other
#    laws and arguments, the lap bound 1,700,000 ms, one lap, the run's bound the lap's and 300 s), with its held joint
#    (FIELD_JOINT_NATS) and lane2.sh's reads (the order, the openings on HELD128 and TRAIN, the one-end and keyed writers), read
#    with the clock.
# 2. On the new state, read with the clock: the keyed locks given held's lengths for held 0-31 and the parallel certified exchange
#    to rest from them (settle-field: its KEYED.tsv is the keyed write, refine 0, and its SAMPLE.tsv the rest); then the point
#    re-draws from that rest (redraw-field, where field_pass.redraw is executable: its parity passed).
# 3. The state charge census on the keyed locks and the rest (charge.sh STATE TAG KEYED REST).
# 4. One summary line: the held joint, code and entropy a place at the locks and the rest, the re-draws' stop, and the v > 2
#    shares (the lock and phase reads are left to the caller's scripts).
# Projections: the lap as lane2.sh's (1,700 s, outer the bound and 300 s and 60 s); the reads as lane2.sh's own timeouts; the
# settle and the re-draws at the settle's measured largest pass (27.6 s) times their defect bound of 1,000 passes and 60 s, each
# deadline 1.25 x (a guard: each stops at rest or neutrality).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-09-nov6-field-resumes; BIN=$O/field_pass; F84=$R/2026-11-05-code84
X=$R/2026-11-09-exchange; SETTLE=$X/field_pass.settle; REDRAW=$X/field_pass.redraw
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
LOCK=$ROOT/.local/gpu.lock
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; E=$O/HELD_ENDS.tsv
RB=$O/field_pass.reads
[ $# -eq 2 ] || { echo "lane_lap.sh FROM NAME"; exit 2; }
FROM=$1; NAME=$2
[ -e $O/STOP ] && { echo "MAIN STOP read: the lap $NAME is not begun $(date -u +%H:%M:%S)"; exit 0; }
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
# A stage on the card: the lock taken for it alone.
card() { # STAGE COMMAND...
  local stage=$1; shift
  ( flock -w 14400 9 || { echo "MAIN LOCK_BUSY at $stage"; exit 75; }; echo "# $stage: lock taken $(date -u +%H:%M:%S)"; "$@" ) 9>$LOCK
}
judge_write() { # DIR NAME
  grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $1/$2.log | cut -c1-200
  python3 -I $O/collapse.py $P/HELD128.txt $1/$2/SAMPLE.tsv | head -1
  python3 -I $O/code_reading.py $P/HELD128.txt $1/$2/SAMPLE.tsv | sed -n 2p
  python3 -I $O/code_closure.py $P/HELD128.txt $1/$2/SAMPLE.tsv
}
L=1700000; SEG=$(( L + 300000 )); OUTER=$(( SEG / 1000 + 60 ))
echo "# $NAME from $(sha $FROM): $(head -1 $FROM | cut -c1-40); binary $(sha $BIN); lap bound $L ms, the run's $SEG ms, outer $OUTER s $(date -u +%H:%M:%S)"
case $FROM in *lane27_28*|*lane30_32*) echo "# LABEL no bare clock: the lane's laps train without FIELD_CLOCK_BARE (lane2.sh's law); the reads keep it";; esac
# 1. The lap.
rm -rf $O/$NAME
card lap env -u FIELD_CLOCK_BARE FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M $NAME timeout $OUTER $BIN train complete-language train-field $T 32 4 8 2 32 4 16 1 8 $L $L $SEG $O/$NAME $FROM $(sha $FROM) > $O/$NAME.log 2>&1
grep -E '^FIELD_(LAPS_HELD|STOPPED)|^FIELD_LAP |^FIELD_JOINT_NATS|^MEASURE|rror|panic' $O/$NAME.log | sed -E 's/ sites=[0-9]+//' | cut -c1-220
S=$(ls -t $O/$NAME/STATE.* 2>/dev/null | grep -v stopped | head -1)
[ -n "$S" ] || { echo "MAIN $NAME made no state"; exit 1; }
echo "# the new state $(basename $S) $(sha $S)"
# The lap's reads, lane2.sh's.
rm -rf $O/${NAME}_order $O/${NAME}_HELD128 $O/${NAME}_TRAIN $O/${NAME}_place $O/${NAME}_keyed
card order $M ${NAME}_order timeout 900 $RB train complete-language order-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 $O/${NAME}_order > $O/${NAME}_order.log 2>&1
for set in HELD128 TRAIN; do
  card opening_$set $M ${NAME}_$set timeout 300 $RB train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/$set.txt $(sha $P/$set.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) 128 $O/${NAME}_$set > $O/${NAME}_$set.log 2>&1
done
card place env FIELD_WRITER_ONE_END=1 FIELD_WRITER_RUN_BITS=1 $M ${NAME}_place timeout 900 $RB train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/${NAME}_place > $O/${NAME}_place.log 2>&1
card keyed env FIELD_WRITER_LENGTHS=$E FIELD_WRITER_RUN_BITS=1 $M ${NAME}_keyed timeout 900 $RB train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/${NAME}_keyed > $O/${NAME}_keyed.log 2>&1
echo "== order $(grep -E '^FIELD_ORDER|^MEASURE|rror|panic' $O/${NAME}_order.log | tr '\n' ' ' | cut -c1-400)"
python3 -I $O/marginal.py $O/${NAME}_order/ORDER.tsv $O/${NAME}_HELD128/LENGTHS.tsv
for set in HELD128 TRAIN; do
  echo "== $set"
  python3 -I $O/opening.py $O/${NAME}_$set | grep -vE '^problem|^[0-9]+\s'
done
python3 -I $O/overrun.py $O/${NAME}_HELD128 $O/${NAME}_TRAIN
python3 -I $O/conditioned.py $O/${NAME}_HELD128 $O/${NAME}_TRAIN
echo "== write place (the one-end writer, read)"
python3 -I $O/endings.py $P/HELD128.txt $O/${NAME}_place/SAMPLE.tsv 2062
judge_write $O ${NAME}_place
echo "== write keyed given held's lengths (judged)"
judge_write $O ${NAME}_keyed
# 2. The keyed locks and the parallel exchange to rest, then the point re-draws.
APASS=27600; BOUND=1000; PROJ=$(( BOUND * APASS / 1000 + 60 )); DEAD=$(( PROJ * 5 / 4 ))
WRITE="$S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062"
rm -rf $O/${NAME}_settle
card settle env FIELD_WRITER_LENGTHS=$E FIELD_WRITER_RUN_BITS=1 $M ${NAME}_settle timeout $DEAD $SETTLE train complete-language settle-field $WRITE 1000 $BOUND $O/${NAME}_settle > $O/${NAME}_settle.log 2>&1
echo "== the keyed locks settled to rest"
grep -E '^FIELD_SETTLE_DONE|^MEASURE|rror|panic|refused' $O/${NAME}_settle.log | cut -c1-320
KEYED=$O/${NAME}_settle/KEYED.tsv; REST=$O/${NAME}_settle/SAMPLE.tsv
[ -f $KEYED ] && [ -f $REST ] || { echo "MAIN the settle left no locks or rest"; exit 1; }
cmp -s $KEYED $O/${NAME}_keyed/SAMPLE.tsv && echo "# the settle's keyed write is the keyed locks' (${NAME}_keyed/SAMPLE.tsv)" || echo "# the settle's keyed write differs from ${NAME}_keyed/SAMPLE.tsv"
if [ -x $REDRAW ]; then
  rm -rf $O/${NAME}_redraw
  card redraw $M ${NAME}_redraw timeout $DEAD $REDRAW train complete-language redraw-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 $REST $(sha $REST) 1000 $BOUND $O/${NAME}_redraw > $O/${NAME}_redraw.log 2>&1
  echo "== the point re-draws from the rest"
  grep -E '^FIELD_REDRAW_DONE|^MEASURE|rror|panic|refused' $O/${NAME}_redraw.log | cut -c1-320
  D=$(grep -cE '^FIELD_REDRAW .* stop=bound' $O/${NAME}_redraw.log); [ "$D" -eq 0 ] || echo "# DEFECT: $D problems stopped by the $BOUND-pass defect bound"
else
  echo "# the re-draws are not run: field_pass.redraw is not executable (its parity has not passed)"
fi
# 3. The state charge census on the locks and the rest.
bash $X/charge.sh $S ${NAME}_charge $KEYED $REST
# 4. The summary.
J=$(grep -E '^FIELD_JOINT_NATS' $O/$NAME.log | tail -1 | sed -E 's/.*own_nats_a_place=([0-9.]+).*/\1/')
CL=$X/${NAME}_charge/charge.log
st() { grep -E "^FIELD_CHARGE_STATE state=$1 " $CL 2>/dev/null | sed -E 's/.*code_nats_a_place=([0-9.]+) entropy_nats_a_place=([0-9.]+).*v_over_2_share=([0-9.]+).*/\1\/\2 v2=\3/'; }
RD=$(grep -E '^FIELD_REDRAW_DONE' $O/${NAME}_redraw.log 2>/dev/null | sed -E 's/.*neutral=([0-9]+) rested=([0-9]+).*code_end_nats_a_place=([0-9.]+) entropy_end_nats_a_place=([0-9.]+).*/\3\/\4 neutral=\1 rested=\2/')
RV=$(grep -E '^FIELD_REDRAW_PASS' $O/${NAME}_redraw.log 2>/dev/null | tail -1 | sed -E 's/.*v_over_2_share=([0-9.]+).*/\1/')
echo "LAP $NAME joint=${J:-?} locks=$(st keyed) rest=$(st rest) redraw=${RD:-not-run} redraw_v2=${RV:-?} $(date -u +%H:%M:%S)"
echo "MAIN exit $(date -u +%H:%M:%S)"
