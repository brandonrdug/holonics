#!/bin/bash
# The line on a redrawn arithmetic slice (the lead, November 16; guesses G-V1 to G-V4 fixed first): chain 22 is ended in the gap after lap G
# (its loudness read printed, its forms watcher's GSM8K writes printed), lap G's last state is moved to the store whose arithmetic slice was
# redrawn (move-store: operand lengths, operand counts and operations at the word problems' own counts, documents of 1 to 32 records by
# octaves) and its world is set to one act in 21 of the slice's stretches (set-world: the redrawn slice cuts into 4.4 times the stretches a
# place and 2.6 times the acts, by the cut's simulation, so 8 becomes 21 to hold the world's share of a section), and laps G+1 to 83 run with
# chain 22's binary (athena_acts: no law of the engine changes; the terrain and the pass's place alone). One life. Where the first lap on the
# redrawn slice ends without a pass or a stop line, it is set aside and the lap is run again from lap G's last state on the old store, as
# chain 22 would have run it, and the chain goes on there. Projection: a lap about as lap 77 (the section's sites bind; its pairs fall by
# about a tenth, its regions about double); the lap's stop bound 3,300,000 ms and deadline 3,600 s, 1,200 s a read.
set -u
G=$1
ROOT=ROOT; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line; R=$ROOT/.local/wt/lead/.local/run/tension
S0=$ROOT/.local/corpus/store-2026-11-16; S1=$ROOT/.local/corpus/store-2026-11-16b; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$ROOT/.local/wt/store-trainer/.local/run/p48
M="python3 -I $ROOT/tools/measure.py"; LOCK=$ROOT/.local/gpu.lock
sha() { sha256sum "$1" | cut -c1-64; }
H=$P/HELD128.txt; C2=$R2/g115r2/CODEC; C=$R2/g115r1/CODEC
BIN=$ROOT/.local/wt/depth-sweep/.local/run/mark/bin/athena_acts; TOOL=$R/bin/athena_tension9
S=$S1
cavity() {
  local n=$1 mean=$2
  env -i HOME=$HOME PATH=$PATH $M P$n timeout 1200 $BIN train complete-language read-cavity $U0 $(sha $U0) $S $(sha $S/STORE.tsv) $K $(sha $K) $C $(sha $C) 20000 $mean $(sha $mean) $Q/out_P$n > $Q/P$n.log 2>&1
  grep -hE '^CAVITY_DONE|^MEASURE|rror' $Q/P$n.log | cut -c1-160
}
loud() {
  local n=$1 mean=$2
  env -i HOME=$HOME PATH=$PATH $M loud$n timeout 1200 $BIN train complete-language read-loudness $U0 $(sha $U0) $S $(sha $S/STORE.tsv) $K $(sha $K) $C $(sha $C) 20000 $mean $(sha $mean) $Q/loud_P$n > $Q/loud_P$n.log 2>&1
  python3 -I $ROOT/tools/loudness_table.py $Q/loud_P$n > $Q/loud_P$n.table 2>&1
  echo "# loud$n: $(date -u +%H:%M:%S) on ${mean#$Q/}"; grep -hE '^MEASURE|rror' $Q/loud_P$n.log | cut -c1-160; grep -E "^LOUDNESS region=all" $Q/loud_P$n.table | cut -c1-160
}
mean_of() { local km; km=$(ls $Q/lap$1/ 2>/dev/null | sed -n "s/^MEAN\.\([0-9]*\)$/\1/p" | sort -n | tail -1); [ -n "$km" ] && echo $Q/lap$1/MEAN.$km; }
last_of() { local k; k=$(ls $Q/lap$1/ 2>/dev/null | sed -n "s/^STATE\.\([0-9]*\)$/\1/p" | sort -n | tail -1); [ -e $Q/lap$1/STATE.stopped ] && { echo $Q/lap$1/STATE.stopped; return; }; [ -n "$k" ] && echo $Q/lap$1/STATE.$k; }
lap() {
  local n=$1 src=$2
  ( flock -w 14400 9 || exit 75; echo "# lap$n: lock taken $(date -u +%H:%M:%S) from ${src#$ROOT/} on ${S##*/}"
    env -i HOME=$HOME PATH=$PATH $M lap$n timeout 3600 $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $S/STORE.tsv) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 3000 1000 3300000 $Q/lap$n $src $(sha $src) > $Q/lap$n.log 2>&1
    echo "# lap$n: exit $? released $(date -u +%H:%M:%S)" ) 9>$LOCK
  grep -E '^MEASURE|rror|panic|^STORE_PASS |^STORE_STOPPED' $Q/lap$n.log | cut -c1-260
}
N=$((G + 1))
[ -x $BIN ] && [ -x $TOOL ] && [ -e $S1/STORE.tsv ] || { echo "MAIN STOP a binary or the redrawn store is missing"; exit 1; }
for f in STATE.moved$N STATE.world$N; do [ -e $Q/$f ] && { echo "MAIN STOP $Q/$f exists"; exit 1; }; done
until grep -q "^# loud$G:" $Q/line-twenty-two.out 2>/dev/null || grep -q '^MAIN' $Q/line-twenty-two.out 2>/dev/null; do sleep 1; done
grep -q '^MAIN' $Q/line-twenty-two.out && { echo "MAIN STOP chain 22 ended before lap $G's loudness: $(grep '^MAIN' $Q/line-twenty-two.out)"; exit 1; }
python3 $ROOT/tools/runs.py stop line-twenty-two; echo "# stopped line-twenty-two $(date -u +%H:%M:%S); lap$N begun: $([ -e $Q/lap$N ] && echo yes || echo no)"
[ -e $Q/lap$N ] && { echo "MAIN STOP lap$N was begun by chain 22"; exit 1; }
until grep -q "^# wg$G" $Q/forms-twenty-two.out 2>/dev/null; do sleep 2; done
python3 $ROOT/tools/runs.py stop forms-twenty-two; echo "# stopped forms-twenty-two $(date -u +%H:%M:%S)"
src0=$(last_of $G) || { echo "MAIN STOP no state in lap$G"; exit 1; }
moved=$src0
if $TOOL train complete-language move-store $src0 $(sha $src0) $S1 $(sha $S1/STORE.tsv) arithmetic $Q/STATE.moved$N > $Q/moved$N.log 2>&1 \
  && $BIN train complete-language set-world $Q/STATE.moved$N $(sha $Q/STATE.moved$N) arithmetic 21 1 48 $Q/STATE.world$N 1 > $Q/world$N.log 2>&1; then
  echo "# move-store from ${src0#$Q/}: $(grep MOVE_STORE $Q/moved$N.log | cut -c1-400)"; echo "# set-world: $(grep SET_WORLD $Q/world$N.log | cut -c1-200)"
  moved=$Q/STATE.world$N
else
  echo "# the move failed: $(tail -2 $Q/moved$N.log $Q/world$N.log 2>/dev/null | cut -c1-300)"; S=$S0
fi
for n in $(seq $N 83); do
  if [ $n -eq $N ]; then src=$moved; else
    src=$(last_of $((n - 1))) || { echo "MAIN STOP no state in lap$((n - 1))"; exit 1; }
    if grep -q "ended=true" $Q/lap$((n - 1)).log 2>/dev/null; then
      $BIN train complete-language next-pass $src $(sha $src) $Q/STATE.next$n > $Q/next$n.log 2>&1 || { echo "MAIN STOP next-pass failed"; cat $Q/next$n.log; exit 1; }
      echo "# next-pass before lap$n $(tail -1 $Q/next$n.log | cut -c1-120)"; src=$Q/STATE.next$n
    fi
  fi
  echo "# binary ${BIN##*/}"
  [ -e $Q/lap$n ] && { echo "MAIN STOP $Q/lap$n exists"; exit 1; }
  lap $n $src
  if [ $n -eq $N ] && [ $S = $S1 ] && ! grep -qE '^STORE_PASS |^STORE_STOPPED ' $Q/lap$n.log; then
    echo "# lap$n on the redrawn slice ended with no pass or stop line: set aside, and run again on the old store from ${src0#$Q/}"
    mv $Q/lap$n $Q/lap$n.redrawn-failed 2>/dev/null; mv $Q/lap$n.log $Q/lap$n.redrawn-failed.log
    S=$S0; lap $n $src0
  fi
  m=$(mean_of $n) || { echo "MAIN STOP no mean in lap$n"; exit 1; }
  cavity $n $m; loud $n $m
done
echo "MAIN lane line twenty-three done $(date -u +%H:%M:%S)"
