#!/usr/bin/env bash
# m7 of the throw's control chain from m6-coordinate.state, outer cap 4049 s, stderr lines wall-stamped
# (ms since process start), stack samples by gdb every 300 s.
cd /home/user/holonics/.local/wt/diag
out=.local/diag-m7
bin=target/release/examples/hnn_prediction
unset EXCURSION_CHECKPOINT
{ git rev-parse HEAD; sha256sum $bin | cut -d' ' -f1; sha256sum $out/in.state; echo "args executed move-once order2 2026093061 8 $out m7=$out/in.state lock-dec coordinate"; echo "RAYON_NUM_THREADS=4 timeout 4049"; } > $out/identities.txt
start=$(date +%s%3N)
( RAYON_NUM_THREADS=4 timeout 4049 $bin executed move-once order2 2026093061 8 $out m7=$out/in.state lock-dec coordinate > $out/listing.txt 2> >(while IFS= read -r line; do echo "$(( $(date +%s%3N) - start )) $line"; done > $out/stderr.stamped) ; echo "exit $?" > $out/exit.txt ) &
sleep 2
pid=$(pgrep -f "hnn_prediction executed move-once order2 2026093061 8 $out" | head -1)
echo "pid $pid" >> $out/identities.txt
n=0
while kill -0 $pid 2>/dev/null; do
  sleep 300
  kill -0 $pid 2>/dev/null || break
  n=$((n+1))
  { echo "== sample $n at $(( $(date +%s%3N) - start )) ms"; gdb -p $pid -batch -ex "thread apply all bt 25" 2>/dev/null | grep -E '^Thread|^#' | sed -E 's/ \(.*\) at / at /' ; } >> $out/stacks.txt
done
wait
echo "wall $(( $(date +%s%3N) - start )) ms; $(cat $out/exit.txt)" >> $out/identities.txt
