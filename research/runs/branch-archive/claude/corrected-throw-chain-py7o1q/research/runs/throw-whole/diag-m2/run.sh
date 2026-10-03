#!/usr/bin/env bash
cd /home/user/holonics
d=.local/diag-m2
start=$(date +%s%3N)
RAYON_NUM_THREADS=4 timeout 4049 target/release/examples/hnn_prediction executed move-once order2 2026093061 8 $d m2=$d/in.state lock-dec throw > $d/listing.txt 2> $d/stderr.txt &
tpid=$!
sleep 5
pid=$(pgrep -P $tpid)
echo "pid $pid" 
n=0
while kill -0 $tpid 2>/dev/null; do
  sleep 115
  kill -0 $pid 2>/dev/null || break
  n=$((n+1)); t=$(( ($(date +%s%3N) - start) / 1000 ))
  { echo "sample $n at ${t} s"; gdb -batch -p $pid -ex "thread apply all bt 40" 2>&1 | grep -E "^#|^Thread"; } > $d/stacks/s$(printf %02d $n).txt
  echo "sample $n at ${t} s: $(grep -m1 -oE 'in holonics::[^ (]+' $d/stacks/s$(printf %02d $n).txt | head -1)"
done
wait $tpid; status=$?
echo "diag done: exit $status; wall $(( $(date +%s%3N) - start )) ms"
