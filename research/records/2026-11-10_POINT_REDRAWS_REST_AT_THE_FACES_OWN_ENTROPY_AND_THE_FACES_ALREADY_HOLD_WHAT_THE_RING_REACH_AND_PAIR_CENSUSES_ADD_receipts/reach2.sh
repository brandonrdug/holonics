#!/bin/bash
# reach2.sh STATE TAG [LINE_LOG]: the reach census on census 2b's charge set (theory, November 10 04:40; claude/exchange-walk, the
# commit in BUILD.reach2), with long114's laws, every output under $O/TAG/. reach2-field: one forward visit of the state's own lap
# (census 2b's partly locked training states, its checks first: check 1 on the reference pair, long114 seg10 STATE.1 against
# lap25_26.log's FIELD_SECTION lap=0 n=0, one section; then STATE against LINE_LOG's line where given, else NO_LINE; the charge
# over the visit), at the answer sites it charges of TRAIN's spread sample (every 6th problem of each parity of the index), and
# the held problems' own joint states (every open place). At each site t and each offset d = +-1, 2, 3, 4, 6, 8, ..., 192, 256:
# the letter at t + d where it is locked, a blank where it is open, the void past the region's ends, against the letter at t.
# REACH2.tsv (set, d, far, letter, n, f) and FIELD_REACH2 a line per (set, d): U a place and the places. Numbers only.
# Projection: census 2b's whole-lap visit at its largest measured section (600 ms) x 1,535 sections, 921 s, and the sums, the held
# read and the table, 240 s: 1,161 s; deadline 1.25 x, 1,451 s. RTX 4080 SUPER under .local/gpu.lock (flock -w 14400); host
# threads 8.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-09-census2; BIN=$O/field_pass.reach2
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
[ $# -eq 2 ] || [ $# -eq 3 ] || { echo "reach2.sh STATE TAG [LINE_LOG]"; exit 2; }
S=$1; TAG=$2
O=$O/$TAG; mkdir -p $O
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
line_of() { # LOG STATE
  grep -m1 -E '^FIELD_COMMAND train-field ' $1 | grep -qF "$(sha $2)" || { echo "-"; return; }
  grep -qE '^FIELD_(LANE|GROW) lap=-1' $1 && { echo "-"; return; }
  grep -m1 -E '^FIELD_SECTION lap=0 n=0 ' $1 | sed -E 's/.* sites=([0-9]+) before=([0-9.]+) .*/\1:\2/' | grep -E '^[0-9]+:[0-9.]+$' || echo "-"
}
RS=$R/2026-11-06-long114/seg10/STATE.1; RL=$R/2026-11-09-nov6-field-resumes/lap25_26.log
REF=$(line_of $RL $RS)
LINE="-"; [ $# -eq 3 ] && LINE=$(line_of $3 $S)
PROJ=1161; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $(dirname $BIN)/BUILD.reach2 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); its line $LINE; the reference pair's line $REF; projected $PROJ s, deadline $DEAD s"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the census reads it on the declared bare clock";; esac
[ "$REF" != "-" ] || { echo "MAIN no line for the reference pair in $RL: check 1 cannot be read"; exit 1; }
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1 RAYON_NUM_THREADS=8
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
reach2() { # NAME STATE SECTIONS LINE DEADLINE
  rm -rf $O/$1
  $M $1 timeout $5 $BIN train complete-language reach2-field $T 16 $3 $2 $(sha $2) $4 6 $O/$1 > $O/$1.log 2>&1
  grep -E '^FIELD_CLOCKS|^FIELD_CHECK|^FIELD_REACH2 |^FIELD_REACH2_DONE|^MEASURE|rror|panic|refused' $O/$1.log | cut -c1-240
}
passed() { # NAME
  grep -q '^FIELD_CHECK check=1 result=\(PASS\|NO_LINE\) ' $O/$1.log && grep -q '^FIELD_CHECK check=2 result=PASS ' $O/$1.log && [ $(grep -c '^FIELD_CHECK check=3 part=[a-z_]* result=PASS ' $O/$1.log) -eq 2 ] && grep -q '^FIELD_REACH2_DONE' $O/$1.log
}
echo "== check 1 on the reference pair (long114 seg10 STATE.1, lap25_26.log's FIELD_SECTION lap=0 n=0 $REF): one section"
reach2 check_ref $RS 1 $REF 600 > /dev/null
grep -E '^FIELD_CHECK' $O/check_ref.log | cut -c1-200
grep -q '^FIELD_CHECK check=1 result=PASS ' $O/check_ref.log && passed check_ref || { echo "MAIN a check failed on the reference pair: the reach census not read"; exit 1; }
echo "== the reach census on 2b's charge set, the whole lap"
reach2 reach2 $S 0 $LINE $DEAD
passed reach2 || { echo "MAIN a check failed or the census did not finish"; exit 1; }
ls -la $O/reach2/
echo "MAIN exit $(date -u +%H:%M:%S)"
