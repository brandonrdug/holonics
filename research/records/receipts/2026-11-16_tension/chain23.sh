#!/bin/bash
# The four-lane line with the triads' legs founded where the tension leads (the lead, November 16; the founding law of October 24, atlas
# contact.pool-founding, on the engine's crossing triads): chain 22's steps (gate 3 for the build with the draft refine, the world set to one
# record a prompt with the refine on, parity, a dev read, laps 77 to 83, each with its reads) with one step more in the hold. After set-world,
# found-crossing writes STATE.found77 from STATE.acts77: the ten triads' legs located by tools/tension_ruler.py from the covector at the
# strand's return over four of lap 76's own sections (read-tension-store on lap 76's MEAN.1000, host), their return W_T at zero and their
# moments opened as a growth opens them, every other entry, moment, rate and line kept. With W_T at zero every face reads bit for bit as
# STATE.acts77's: held here by read-forms on the host over the 686 held forms, both states, line for line. Where the founding or that check
# fails the chain trains from STATE.acts77 as chain 22 would have (FOUND FALLBACK), so the card does not wait. One life. Projection as chain
# 22's: gate 3 about 9 minutes, the founding and its check about 1, the parity about 4, the dev read about 1; a lap about 2,500 s, its reads
# about 560 s. The lap's stop bound 3,300,000 ms and deadline 3,600 s, 1,200 s a read, 1,800 s a step.
set -u
ROOT=ROOT; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
S=$ROOT/.local/corpus/store-2026-11-16; P=$ROOT/.local/data/python-codes-25k/passage; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$ROOT/.local/wt/store-trainer/.local/run/p48
M="python3 -I $ROOT/tools/measure.py"; LOCK=$ROOT/.local/gpu.lock
sha() { sha256sum "$1" | cut -c1-64; }
H=$P/HELD128.txt; ST=$S/STORE.tsv; C2=$R2/g115r2/CODEC; C=$R2/g115r1/CODEC
BIN=$ROOT/.local/wt/depth-sweep/.local/run/mark/bin/athena_acts
T=$ROOT/.local/wt/lead/.local/run/tension; TOOL=$T/bin/athena_tension2; LEGS=$T/found76.legs; FA=$S/FORMS_arithmetic5.tsv
cavity() {
  local n=$1 mean=$2
  env -i HOME=$HOME PATH=$PATH $M P$n timeout 1200 $BIN train complete-language read-cavity $U0 $(sha $U0) $S $(sha $ST) $K $(sha $K) $C $(sha $C) 20000 $mean $(sha $mean) $Q/out_P$n > $Q/P$n.log 2>&1
  grep -hE '^CAVITY_DONE|^MEASURE|rror' $Q/P$n.log | cut -c1-160
}
loud() {
  local n=$1 mean=$2
  env -i HOME=$HOME PATH=$PATH $M loud$n timeout 1200 $BIN train complete-language read-loudness $U0 $(sha $U0) $S $(sha $ST) $K $(sha $K) $C $(sha $C) 20000 $mean $(sha $mean) $Q/loud_P$n > $Q/loud_P$n.log 2>&1
  python3 -I $ROOT/tools/loudness_table.py $Q/loud_P$n > $Q/loud_P$n.table 2>&1
  echo "# loud$n: $(date -u +%H:%M:%S) on ${mean#$Q/}"; grep -hE '^MEASURE|rror' $Q/loud_P$n.log | cut -c1-160; grep -E "^LOUDNESS region=all" $Q/loud_P$n.table | cut -c1-160
}
mean_of() { local km; km=$(ls $Q/lap$1/ 2>/dev/null | sed -n "s/^MEAN\.\([0-9]*\)$/\1/p" | sort -n | tail -1); [ -n "$km" ] && echo $Q/lap$1/MEAN.$km; }
last_of() { local k; k=$(ls $Q/lap$1/ 2>/dev/null | sed -n "s/^STATE\.\([0-9]*\)$/\1/p" | sort -n | tail -1); [ -e $Q/lap$1/STATE.stopped ] && { echo $Q/lap$1/STATE.stopped; return; }; [ -n "$k" ] && echo $Q/lap$1/STATE.$k; }
until grep -q '^# wg76' $Q/forms-twenty-one.out 2>/dev/null && grep -q '^# stopped line-twenty-one' $Q/stop21.out 2>/dev/null; do sleep 5; done
[ -e $Q/lap77 ] && { echo "MAIN STOP lap77 was begun by chain 21"; exit 1; }
[ -x $BIN ] || { echo "MAIN STOP no binary $BIN"; exit 1; }
for f in gate_acts STATE.acts77 STATE.found77 parity_acts dev_acts start77.txt; do [ -e $Q/$f ] && { echo "MAIN STOP $Q/$f exists"; exit 1; }; done
src=$(last_of 76) || { echo "MAIN STOP no state in lap76"; exit 1; }
( flock -w 14400 9 || exit 75; echo "# hold: lock taken $(date -u +%H:%M:%S)"
  bash $ROOT/.local/wt/arithworld/tools/gate_engine.sh $ROOT/.local/wt/arithworld/.local/line17.env $BIN $Q/gate_acts > $Q/gate_acts.log 2>&1
  echo "# gate3 $(date -u +%H:%M:%S): $(grep -E '^GATE_ENGINE' $Q/gate_acts.log)"
  grep -q '^GATE_ENGINE EQUAL' $Q/gate_acts.log || { echo "MAIN STOP gate 3 not equal"; exit 1; }
  $BIN train complete-language set-world $src $(sha $src) arithmetic 8 1 48 $Q/STATE.acts77 1 > $Q/acts77.log 2>&1 || { echo "MAIN STOP set-world failed"; cat $Q/acts77.log; exit 1; }
  echo "# set-world from ${src#$Q/}: $(grep SET_WORLD $Q/acts77.log)"
  start=$Q/STATE.acts77
  if [ -s $LEGS ] && $TOOL train complete-language found-crossing $Q/STATE.acts77 $(sha $Q/STATE.acts77) $LEGS $(sha $LEGS) $Q/STATE.found77 > $Q/found77.log 2>&1; then
    echo "# found-crossing: $(grep FOUND_CROSSING $Q/found77.log)"
    for st in acts77 found77; do
      env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=10 timeout 600 $TOOL host complete-language read-forms $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $FA $(sha $FA) $Q/STATE.$st $(sha $Q/STATE.$st) > $Q/faces_$st.log 2>&1
    done
    if [ "$(grep -c '^FORMS_ROW' $Q/faces_acts77.log)" -gt 0 ] && cmp -s <(grep '^FORMS_ROW' $Q/faces_acts77.log) <(grep '^FORMS_ROW' $Q/faces_found77.log); then
      echo "# faces $(date -u +%H:%M:%S): EQUAL rows=$(grep -c '^FORMS_ROW' $Q/faces_found77.log)"; start=$Q/STATE.found77
    else
      echo "# faces $(date -u +%H:%M:%S): NOT EQUAL; FOUND FALLBACK to STATE.acts77"
    fi
  else
    echo "# FOUND FALLBACK to STATE.acts77: $(tail -1 $Q/found77.log 2>/dev/null | cut -c1-160)"
  fi
  echo "$start" > $Q/start77.txt
  env -i HOME=$HOME PATH=$PATH $M parity_acts timeout 1800 $BIN parity complete-language parity-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 3 3 1800000 $Q/parity_acts $start $(sha $start) > $Q/parity_acts.log 2>&1
  echo "# parity $(date -u +%H:%M:%S): $(grep -E '^STORE_PARITY_DONE|rror|panic' $Q/parity_acts.log | cut -c1-200)"
  grep -q '^STORE_PARITY_DONE .*EQUAL' $Q/parity_acts.log || { echo "MAIN STOP parity not equal"; exit 1; }
  env -i HOME=$HOME PATH=$PATH $M dev_acts timeout 600 $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 24 24 540000 $Q/dev_acts $start $(sha $start) > $Q/dev_acts.log 2>&1
  echo "# dev $(date -u +%H:%M:%S): $(grep -E '^MEASURE|rror|panic' $Q/dev_acts.log | cut -c1-200)"
) 9>$LOCK || { echo "MAIN STOP the hold failed"; exit 1; }
for n in 77 78 79 80 81 82 83; do
  if [ $n -eq 77 ]; then src=$(cat $Q/start77.txt); else
    src=$(last_of $((n - 1))) || { echo "MAIN STOP no state in lap$((n - 1))"; exit 1; }
    if grep -q "ended=true" $Q/lap$((n - 1)).log 2>/dev/null; then
      $BIN train complete-language next-pass $src $(sha $src) $Q/STATE.next$n > $Q/next$n.log 2>&1 || { echo "MAIN STOP next-pass failed"; cat $Q/next$n.log; exit 1; }
      echo "# next-pass before lap$n $(tail -1 $Q/next$n.log | cut -c1-120)"; src=$Q/STATE.next$n
    fi
  fi
  echo "# binary ${BIN##*/}"
  [ -e $Q/lap$n ] && { echo "MAIN STOP $Q/lap$n exists"; exit 1; }
  ( flock -w 14400 9 || exit 75; echo "# lap$n: lock taken $(date -u +%H:%M:%S) from ${src#$ROOT/}"
    env -i HOME=$HOME PATH=$PATH $M lap$n timeout 3600 $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 3000 1000 3300000 $Q/lap$n $src $(sha $src) > $Q/lap$n.log 2>&1
    echo "# lap$n: exit $? released $(date -u +%H:%M:%S)" ) 9>$LOCK
  grep -E '^MEASURE|rror|panic|^STORE_PASS |^STORE_STOPPED' $Q/lap$n.log | cut -c1-260
  m=$(mean_of $n) || { echo "MAIN STOP no mean in lap$n"; exit 1; }
  cavity $n $m; loud $n $m
done
echo "MAIN lane line twenty-three done $(date -u +%H:%M:%S)"
