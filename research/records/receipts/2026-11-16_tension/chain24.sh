#!/bin/bash
# The line continued on the redrawn arithmetic slice (the lead, November 17): chain 23 ends after lap 83, and this chain runs laps 84 to 90
# from lap 83's last state with the same binary (athena_acts) on the same store (store-2026-11-16b), each with its reads, so the card does
# not stand idle. No law, state tool or terrain changes here. It waits for chain 23's last line. Projection: a lap about 3,200 s, its reads
# about 560 s; the lap's stop bound 3,300,000 ms and deadline 3,600 s, 1,200 s a read.
set -u
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
until grep -q '^MAIN' $Q/line-twenty-three.out 2>/dev/null; do sleep 10; done
grep -q '^MAIN lane line twenty-three done' $Q/line-twenty-three.out || { echo "MAIN STOP chain 23 did not end cleanly: $(grep '^MAIN' $Q/line-twenty-three.out)"; exit 1; }
[ -x $BIN ] && [ -e $S1/STORE.tsv ] || { echo "MAIN STOP the binary or the store is missing"; exit 1; }
N=84
for n in $(seq $N 90); do
  if true; then
    src=$(last_of $((n - 1))) || { echo "MAIN STOP no state in lap$((n - 1))"; exit 1; }
    if grep -q "ended=true" $Q/lap$((n - 1)).log 2>/dev/null; then
      $BIN train complete-language next-pass $src $(sha $src) $Q/STATE.next$n > $Q/next$n.log 2>&1 || { echo "MAIN STOP next-pass failed"; cat $Q/next$n.log; exit 1; }
      echo "# next-pass before lap$n $(tail -1 $Q/next$n.log | cut -c1-120)"; src=$Q/STATE.next$n
    fi
  fi
  echo "# binary ${BIN##*/}"
  [ -e $Q/lap$n ] && { echo "MAIN STOP $Q/lap$n exists"; exit 1; }
  lap $n $src
  m=$(mean_of $n) || { echo "MAIN STOP no mean in lap$n"; exit 1; }
  cavity $n $m; loud $n $m
done
echo "MAIN lane line twenty-four done $(date -u +%H:%M:%S)"
