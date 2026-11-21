#!/bin/bash
# The reach's second arm (the lead, November 21): W80g from W79t's end with each head's friction of distance and its gate on the receiver's
# own state founded at zero (found-friction ... gate, reach/gate/W79t_gate.3000), beside W80t (W79t's end, no change; trained by reach80 on
# the friction's build, which reproduced W79t's lap at the law off, as this build does: gate 3, reach/gate3g). One change between them.
# Why: W80r's one friction a head and kind moved by a twentieth of a bit in a lap, toward less at head 0's open places, and left the
# answer digits where W80t has them; a linear read of the receiver's state tells where a friction of one bit pays and keeps the
# terrain's gain at a third of the text's price (site_friction.py).
# Guess G-G1 (receipts/2026-11-21_reach/guesses.txt, fixed before this script was dispatched): see the file.
# Device: the card under .local/gpu.lock for the lap and the card reads; the host panels (6 threads each) and the reach read (6) beside.
# Projection: about 0.77 s a section, 3,000 sections 39 minutes (W80r: 760 ms mean); deadline 3,900 s, the trainer's stop 3,600 s;
# the reads about 20 minutes; about 65 minutes in all.
ROOT=${ROOT:?the main checkout}; L=$ROOT/.local/wt/lead; W=$L/.local/run; D=$W/front; X=$D/long; N=$W/temper/night; F=$D/far
S=$ROOT/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$ROOT/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; C=$R2/g115r1/CODEC; H=$ROOT/.local/data/python-codes-25k/passage/HELD128.txt
BIN=$W/reach/gate/athena; LOCK=$ROOT/.local/gpu.lock
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:$PATH "$@"; }
train() { # train NAME SOURCE SECTIONS DEADLINE
  local n=$1 s=$2 k=$3 dl=$4; [ -e $D/arm_$n ] && { echo "TERRAIN STOP arm_$n exists"; exit 1; }
  ( flock -w 14400 9 || exit 75; echo "# arm $n: lock taken $(date -u +%H:%M:%S)"
    card timeout $dl $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $k 1000 2400000 $D/arm_$n $s $(sha $s) > $D/arm_$n.log 2>&1
    echo "# arm $n: exit $? released $(date -u +%H:%M:%S)" ) 9>$LOCK
  grep -E 'rror|panic|efused|^STORE_STOPPED|field_pass:' $D/arm_$n.log | cut -c1-240 | head -5
  echo "TERRAIN_TRAINED $n $(date -u +%H:%M:%S) sections=$(grep -c '^STORE_SECTION ' $D/arm_$n.log) $(grep '^STORE_PASS ' $D/arm_$n.log | grep -o 'ended=[a-z]*')"
}
cav() { # cav NAME STATE
  local n=$1 st=$2; rm -rf $D/out_$n
  [ -s "$st" ] || { echo "TERRAIN missing $n"; return; }
  ( flock -w 14400 9 || exit 75
    card timeout 1800 $BIN train complete-language read-cavity $U0 $(sha $U0) $S $(sha $ST) $K $(sha $K) $C $(sha $C) 20000 $st $(sha $st) $D/out_$n known > $D/cav_$n.log 2>&1 ) 9>$LOCK
  echo "TERRAIN_READ_DONE $n $(date -u +%H:%M:%S) $(grep -hE '^CAVITY_DONE|rror|efused' $D/cav_$n.log | tail -n 2 | tr '\n' ' ' | cut -c1-200) rows_S=$(grep -c '^S' $D/out_$n/frontier.tsv 2>/dev/null)"
}
panels() { # panels NAME STATE
  local n=$1 st=$2; rm -rf $D/n_$n $X/n_$n
  [ -s "$st" ] || return
  env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 1200 $BIN host complete-language write-next $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $N/panel.tsv $(sha $N/panel.tsv) 64 $D/n_$n $st $(sha $st) 48 2>&1 | grep -E 'rror|efus' | cut -c1-160
  ( flock -w 14400 9 || exit 75
    card timeout 900 $BIN train complete-language write-next $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $X/panel_long.tsv $(sha $X/panel_long.tsv) 96 $X/n_$n $st $(sha $st) > $X/w_$n.log 2>&1 ) 9>$LOCK
  echo "TERRAIN_PANEL $n $(date -u +%H:%M:%S) $(cd $N && python3 -I $D/score.py fit.txt $D/n_$n/forms.written | sed 's/mean_copy [0-9.]* *//g; s/^[^ ]* //' | cut -c1-220) || $(cd $X && python3 -I score_long.py $n=$X/n_$n/forms.written | cut -c1-260)"
}
loud() { # loud NAME MEAN
  local n=$1 m=$2; rm -rf $D/loud_$n
  ( flock -w 14400 9 || exit 75
    card timeout 1800 $BIN train complete-language read-loudness $U0 $(sha $U0) $S $(sha $ST) $K $(sha $K) $C $(sha $C) 20000 $m $(sha $m) $D/loud_$n > $D/loud_$n.log 2>&1 ) 9>$LOCK
  python3 -I $L/tools/loudness_table.py $D/loud_$n > $D/loud_$n.table 2>&1
  echo "TERRAIN_LOUD $n $(date -u +%H:%M:%S) $(grep -hE 'rror|efus' $D/loud_$n.log | head -n 1 | cut -c1-160) lines=$(grep -c '' $D/loud_$n.table)"
}
wide() { # wide NAME MEAN: the long panel's 20 prompts drawn 8 times each (wide/panel_wide.tsv), 96 places
  local n=$1 m=$2; rm -rf $D/wide/n_$n
  ( flock -w 14400 9 || exit 75
    card timeout 900 $BIN train complete-language write-next $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $D/wide/panel_wide.tsv $(sha $D/wide/panel_wide.tsv) 96 $D/wide/n_$n $m $(sha $m) > $D/wide/w_$n.log 2>&1 ) 9>$LOCK
  echo "TERRAIN_WIDE $n $(date -u +%H:%M:%S) $(cd $D/wide && python3 -I score_long.py $n=$D/wide/n_$n/forms.written | cut -c1-300)"
}
BIN=$W/reach/gate/athena; T=$W/terrain
trainT() { # trainT NAME SOURCE SECTIONS DEADLINE STOP_MS
  local n=$1 s=$2 k=$3 dl=$4 st=$5; [ -e $D/arm_$n ] && { echo "TERRAIN STOP arm_$n exists"; exit 1; }
  ( flock -w 14400 9 || exit 75; echo "# arm $n: lock taken $(date -u +%H:%M:%S)"
    card timeout $dl $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $k 1000 $st $D/arm_$n $s $(sha $s) > $D/arm_$n.log 2>&1
    echo "# arm $n: exit $? released $(date -u +%H:%M:%S)" ) 9>$LOCK
  grep -E 'rror|panic|efused|^STORE_STOPPED|field_pass:' $D/arm_$n.log | cut -c1-240 | head -5
  echo "TERRAIN_TRAINED $n $(date -u +%H:%M:%S) sections=$(grep -c '^STORE_SECTION ' $D/arm_$n.log) $(grep '^STORE_PASS ' $D/arm_$n.log | grep -o 'ended=[a-z]*')"
}
hostpanel() { # hostpanel NAME MEAN PANEL: a panel written on the host, 32 places
  local n=$1; local m=$2; local p=$3; local o=$T/$(basename $p .tsv)_$1; rm -rf $o
  env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=6 timeout 1500 nice -n 5 $W/reach/gate/athena host complete-language write-next $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $p $(sha $p) 32 $o $m $(sha $m) > $o.log 2>&1
  echo "TERRAIN_HOSTPANEL $n $(basename $p) $(date -u +%H:%M:%S) $(grep -hE 'NEXT_WRITE_DONE|rror|efus' $o.log | head -n 2 | tr '\n' ' ' | cut -c1-140)"
}
reads() { # reads NAME
  local n=$1; local mean_s=$D/arm_$n/MEAN.3000
  [ -s "$mean_s" ] || { echo "TERRAIN missing $n's mean"; return; }
  hostpanel $n $mean_s $T/panel_terrain.tsv &
  hostpanel $n $mean_s $D/pattern/panel_logic.tsv &
  cav mean_$n $mean_s
  panels ${n}_mean $mean_s
  loud $n $mean_s
  wide $n $mean_s
  wait
}
# The reach's read at each lap's mean: the code of the terrain rows' answer digits by two streams (reach/rows.tsv, reach/places.tsv).
reach() { # reach NAME
  local n=$1; local m=$D/arm_$n/MEAN.3000; local o=$W/reach/code_terrain_$n; rm -rf $o
  env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=6 timeout 1500 nice -n 5 $BIN host complete-language read-reach $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $W/reach/rows.tsv $(sha $W/reach/rows.tsv) $m $(sha $m) $o law > $o.log 2>&1
  echo "TERRAIN_REACH $n $(date -u +%H:%M:%S) $(cd $W/reach && python3 -I answer_codes.py $o places.tsv | grep -E 'ANSWER (copy|reverse|sum) ' | tr -s ' ' | tr '\n' '|')"
}
BIN=$W/reach/gate/athena
echo "TERRAIN_T_START $(date -u +%H:%M:%S)"
echo "REACH_GATE_START $(date -u +%H:%M:%S)"
trainT W80g $W/reach/gate/W79t_gate.3000 3000 3900 3600000
echo "REACH_FRICTION W80g $(for k in 1000 2000 3000; do sed -n 3p $D/arm_W80g/STATE.$k | tr ' ' '\n' | tail -n 904 | head -n 8 | tr '\n' ' '; echo -n '| '; done)"
reach W80g &
reads W80g
wait
echo "TERRAIN_W4G_FRONTIER $(cd $D && python3 -I $L/tools/frontier_ruler.py W80t=out_mean_W80t W80g=out_mean_W80g 2>&1 | grep -E "W80g; (one place open|the frontier:)" | cut -c1-330 | tr '\n' '|')"
cd $T && python3 -I score_terrain.py W80t=panel_terrain_W80t W80g=panel_terrain_W80g | grep SCORE
echo "REACH_GATE_ALL_DONE $(date -u +%H:%M:%S)"
