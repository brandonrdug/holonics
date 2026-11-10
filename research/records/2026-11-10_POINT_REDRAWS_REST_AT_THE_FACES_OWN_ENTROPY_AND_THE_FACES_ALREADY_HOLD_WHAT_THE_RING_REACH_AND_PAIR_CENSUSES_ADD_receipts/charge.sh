#!/bin/bash
# charge.sh STATE TAG [KEYED] [REST]: the state charge census (theory, November 10 03:25; claude/exchange-walk, the commit in BUILD.charge), with
# long114's laws, every output under $O/TAG/. charge-field on held 0-31 in three locked states: the parallel settle's rest
# (settle26/settle/SAMPLE.tsv), its keyed write (settle26/settle/KEYED.tsv) and the held file's references. Each read with every
# place locked (every face once, that place alone open), and at each place v = -ln f_t(x_t) - H(f_t) in nats. Printed a state:
# its code and summed entropy pooled and a problem (FIELD_CHARGE_STATE, FIELD_CHARGE_PROBLEM); the share of places with v > 1 and
# v > 2; the runs of v > 1 by length (1, 2, 3-4, 5-8, ...: length:runs:places) and the share in runs of 3 or more
# (FIELD_CHARGE_RUNS); v by the share of the answer written (tenths, FIELD_CHARGE_WRITTEN); and each answer's root charge
# sum_a N(a) ln(N(a) / sum_t f_t(a)) beside its excess (code - entropy) and its share of it. Numbers only: no text is printed.
# Projection: three locked reads of 32 problems at the walk's measured 15 s a read, and 60 s to load: 105 s; deadline 1.25 x,
# 131 s. RTX 4080 SUPER under .local/gpu.lock (flock -w 14400).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-09-exchange; BIN=$O/field_pass.charge; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
KEYED0=$O/settle26/settle/KEYED.tsv; REST0=$O/settle26/settle/SAMPLE.tsv
[ $# -eq 2 ] || [ $# -eq 4 ] || { echo "charge.sh STATE TAG [KEYED REST]"; exit 2; }
KEYED=${3:-$KEYED0}; REST=${4:-$REST0}  # the keyed locks and the rest (default: lap 26's settle26 files)
S=$1; TAG=$2
O=$O/$TAG; mkdir -p $O
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
[ -f $REST ] && [ -f $KEYED ] || { echo "MAIN the settle's rest or keyed write is missing"; exit 1; }
PROJ=105; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $(dirname $BIN)/BUILD.charge 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); rest $(sha $REST) keyed $(sha $KEYED); projected $PROJ s, deadline $DEAD s"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the census reads it on the declared bare clock";; esac
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
rm -rf $O/charge
$M charge timeout $DEAD $BIN train complete-language charge-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 $REST $(sha $REST) $KEYED $(sha $KEYED) $O/charge > $O/charge.log 2>&1
grep -E '^FIELD_CHARGE_STATE|^FIELD_CHARGE_RUNS|^FIELD_CHARGE_WRITTEN|^FIELD_CHARGE_DONE|^MEASURE|rror|panic|refused' $O/charge.log | cut -c1-320
echo "== each problem"
grep -E '^FIELD_CHARGE_PROBLEM' $O/charge.log | cut -c1-260
echo "MAIN exit $(date -u +%H:%M:%S)"
