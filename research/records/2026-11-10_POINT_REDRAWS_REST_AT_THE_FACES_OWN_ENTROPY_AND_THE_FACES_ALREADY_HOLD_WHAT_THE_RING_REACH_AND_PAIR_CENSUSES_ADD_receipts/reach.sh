#!/bin/bash
# reach.sh STATE TAG [SET]: the reach census (theory, November 10 03:45 and 04:55; claude/exchange-walk, the commit in BUILD.reach),
# with long114's laws, every output under $O/TAG/. reach-census-field on the ring census's locked visit (each reference cut to its
# room, every answer place read once with the rest locked), the spread sets: HELD128, and every 6th problem of each parity of
# TRAIN's index across the whole file (every-6). SET (held, train_even or train_odd) reads that set alone, a partition of the
# work across runs; with no SET all three run in turn. At each answer place t and each offset d = +-1, 2, 3, 4, 6, 8, 12, 16, 24,
# 32, 48, 64, 96, 128, 192, 256: N and F by (the letter at t + d, question letters included, the void past either end) x (the
# letter at t), F the face's share at t on its own width. Each set's REACH.<set>.tsv (set, d, far letter, letter, n, f) is written
# at the end of its set and its FIELD_REACH lines (U a place, sum N ln(N/F) less the same with the far letter pooled) flushed
# there. Numbers only.
# Projection (the first run's measured rate, rc 124 at 2,643 s: held 4 batches in 105 s, TRAIN batches 21-25 s against the 15 s
# first projected): a TRAIN set 64 batches at 25 s, 1,600 s, deadline 2,000 s; held 4 batches, deadline 300 s; all three 3,500 s
# and 120 s to load and write, deadline 4,500 s. RTX 4080 SUPER under .local/gpu.lock (flock -w 14400).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-09-census2; BIN=$O/field_pass.reach; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || [ $# -eq 3 ] || { echo "reach.sh STATE TAG [SET]"; exit 2; }
S=$1; TAG=$2; SET=${3:-}
case "$SET" in held) DEAD=300;; train_even|train_odd) DEAD=2000;; "") DEAD=4500;; *) echo "MAIN a set that is not held, train_even or train_odd"; exit 2;; esac
O=$O/$TAG; mkdir -p $O
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
NAME=reach${SET:+_$SET}
echo "# BUILD $(cat $(dirname $BIN)/BUILD.reach 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); set ${SET:-all}, deadline $DEAD s"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the census reads it on the declared bare clock";; esac
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
rm -rf $O/$NAME
$M $NAME timeout $DEAD $BIN train complete-language reach-census-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) every-6 $SET $O/$NAME > $O/$NAME.log 2>&1
grep -E '^FIELD_REACH |^FIELD_REACH_DONE|^MEASURE|rror|panic|refused' $O/$NAME.log | cut -c1-240
grep -E '^FIELD_REACH_BATCH' $O/$NAME.log | awk 'NR % 16 == 1' | cut -c1-200; grep -E '^FIELD_REACH_BATCH' $O/$NAME.log | tail -1 | cut -c1-200
ls -la $O/$NAME/
echo "MAIN exit $(date -u +%H:%M:%S)"
