#!/bin/bash
# pair.sh STATE TAG PHASEDIR [LINE_LOG]: the pair read (theory, November 10 04:40; claude/exchange-walk, the commit in BUILD.pair),
# with long114's laws, every output under $O/TAG/. pair-field: from the phase census in PHASEDIR (its CENSUS_PHASE.tsv and
# CENSUS_MOMENT.tsv, TRAIN even's rows), for each letter of 2,000 sites or more, tilt = ln Gauss(count cloud) - ln Gauss(face
# cloud) + ln(n/F) over the readout's chart (the clouds' means and covariances in exact rationals, their precisions and
# log-determinants released to the codes' grain); the faces times exp(step x tilt) at steps 1/4, 1/2 and 1 beside the plain ones,
# read on TRAIN's odd problems' answer sites of the lap's own states (census 2b's charge set and its checks; every 6th odd
# problem, the spread sample) as FIELD_PAIR_TRAIN, and on the held joint as FIELD_JOINT_NATS at lap 0 (plain) and 1, 2, 4 (the
# quarters). FIELD_PAIR_LETTER names each letter's sites and constant. Check 1 on the reference pair first, as census 2b's. Numbers
# only.
# Projection: census 2b's whole-lap visit at its largest section (600 ms) x 1,535 sections, 921 s, the tilts' host reads at the
# spread odd sites (about 63,000 integer products a site at 1 ns, about 50 s), the tilts' fraction-free eliminations (24 s measured on 4 host threads, November 10; the rational Gauss-Jordan before them did not
# finish in 900 s, check_ref rc 124) and
# four joint reads (60 s): 1,151 s; deadline 1.25 x, 1,439 s. RTX 4080 SUPER under .local/gpu.lock (flock -w 14400); host
# threads 8.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-09-census2; BIN=$O/field_pass.pair
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
[ $# -eq 3 ] || [ $# -eq 4 ] || { echo "pair.sh STATE TAG PHASEDIR [LINE_LOG]"; exit 2; }
S=$1; TAG=$2; PD=$3
PH=$PD/CENSUS_PHASE.tsv; MO=$PD/CENSUS_MOMENT.tsv
[ -f $PH ] && [ -f $MO ] || { echo "MAIN no phase census tables in $PD"; exit 1; }
O=$O/$TAG; mkdir -p $O
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
line_of() { # LOG STATE
  grep -m1 -E '^FIELD_COMMAND train-field ' $1 | grep -qF "$(sha $2)" || { echo "-"; return; }
  grep -qE '^FIELD_(LANE|GROW) lap=-1' $1 && { echo "-"; return; }
  grep -m1 -E '^FIELD_SECTION lap=0 n=0 ' $1 | sed -E 's/.* sites=([0-9]+) before=([0-9.]+) .*/\1:\2/' | grep -E '^[0-9]+:[0-9.]+$' || echo "-"
}
RS=$R/2026-11-06-long114/seg10/STATE.1; RL=$R/2026-11-09-nov6-field-resumes/lap25_26.log
REF=$(line_of $RL $RS)
LINE="-"; [ $# -eq 4 ] && LINE=$(line_of $4 $S)
PROJ=1151; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $(dirname $BIN)/BUILD.pair 2>/dev/null) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); phase $(sha $PH) moment $(sha $MO); its line $LINE; the reference pair's line $REF; projected $PROJ s, deadline $DEAD s"
case $S in *lane27_28*) echo "# LABEL no bare clock: this state's laps 27-29 trained without FIELD_CLOCK_BARE (the lane growth dropped it); the read keeps the declared bare clock";; esac
[ "$REF" != "-" ] || { echo "MAIN no line for the reference pair in $RL: check 1 cannot be read"; exit 1; }
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1 RAYON_NUM_THREADS=8
exec 9>$ROOT/.local/gpu.lock; flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S)"
pair() { # NAME STATE SECTIONS LINE DEADLINE
  rm -rf $O/$1
  $M $1 timeout $5 $BIN train complete-language pair-field $T 16 $3 $2 $(sha $2) $4 $PH $(sha $PH) $MO $(sha $MO) 6 $O/$1 > $O/$1.log 2>&1
  grep -E '^FIELD_CLOCKS|^FIELD_CHECK|^FIELD_PAIR_TILTS|^FIELD_PAIR_TRAIN|^FIELD_JOINT_NATS|^FIELD_PAIR_DONE|^MEASURE|rror|panic|refused' $O/$1.log | cut -c1-240
}
passed() { # NAME
  grep -q '^FIELD_CHECK check=1 result=\(PASS\|NO_LINE\) ' $O/$1.log && grep -q '^FIELD_CHECK check=2 result=PASS ' $O/$1.log && [ $(grep -c '^FIELD_CHECK check=3 part=[a-z_]* result=PASS ' $O/$1.log) -eq 2 ] && grep -q '^FIELD_PAIR_DONE' $O/$1.log
}
echo "== check 1 on the reference pair (long114 seg10 STATE.1, lap25_26.log's FIELD_SECTION lap=0 n=0 $REF): one section"
pair check_ref $RS 1 $REF 900 > /dev/null
grep -E '^FIELD_CHECK' $O/check_ref.log | cut -c1-200
grep -q '^FIELD_CHECK check=1 result=PASS ' $O/check_ref.log && passed check_ref || { echo "MAIN a check failed on the reference pair: the pair read not read"; exit 1; }
echo "== the pair read, the whole lap"
pair pair $S 0 $LINE $DEAD
grep -E '^FIELD_PAIR_LETTER' $O/pair.log | cut -c1-120 | head -120
passed pair || { echo "MAIN a check failed or the read did not finish"; exit 1; }
echo "MAIN exit $(date -u +%H:%M:%S)"
