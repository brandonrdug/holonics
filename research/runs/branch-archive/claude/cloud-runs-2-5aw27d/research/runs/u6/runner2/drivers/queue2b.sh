#!/usr/bin/env bash
# The second runner's queue after Q4 moved to the PC (coordinator, 21:08): wait for the running Q2 control chain
# (pid 1805), then its held-out read, Q5, Q7.
set -u
cd /home/user/holonics
B=target/release/examples/hnn_prediction
B5=.local/wt/run-end/target/release/examples/hnn_prediction
S=research/runs/u6/states
stamp() { date -u +%FT%TZ; }
sampled() {
  d=$1; shift; mkdir -p $d
  bash out/peak_rss.sh $d/peak_rss.txt & sp=$!
  echo "start $(stamp)" > $d/clock.txt; s=$(date +%s)
  "$@"; rc=$?
  echo "end $(stamp); wall $(( $(date +%s) - s )) s; exit $rc" >> $d/clock.txt
  kill $sp; return $rc
}
while kill -0 1805 2>/dev/null; do sleep 10; done
kill 1801 2>/dev/null
echo "chain end $(stamp) (start 2026-10-02T20:57:28Z)" > out/q2k/clock.txt
echo "Q2k chain done $(stamp)" >> out/queue2.log
fin=$(grep -m1 '^final state' out/q2k/chain.txt | sed 's/^final state //')
mkdir -p out/q2k; echo "final state $fin" > out/q2k/held_clock.txt
sampled out/q2k/held_read env RAYON_NUM_THREADS=4 timeout 5400 $B executed evaluate order2 2026093012 128 out/q2k/held q2k=$fin > out/q2k/held_listing.txt 2> out/q2k/held_stderr.txt
echo "Q2k done $(stamp)" >> out/queue2.log
echo "Q5 $(stamp)" >> out/queue2.log
mkdir -p out/q5
sampled out/q5 env RAYON_NUM_THREADS=4 $B5 executed run order2 2026093061 8 out/q5 m13=$S/r13.state lock-dec kinetic 32 ${Q5_DEADLINE_MS:-60800000} > out/q5/listing.txt 2> out/q5/stderr.txt
echo "Q5 done $(stamp)" >> out/queue2.log
echo "Q7 $(stamp)" >> out/queue2.log
mkdir -p out/q7
for s in 0 1/8 1/4 3/8 1/2 5/8 3/4 7/8 1; do
  n=a$(echo $s | tr / _); mkdir -p out/q7/$n
  sampled out/q7/$n env RAYON_NUM_THREADS=4 timeout 1800 $B executed locks order2 2026093061 8 "a$s=$S/w16.state+$S/fit8_port.txt@102837/131072:$s" lock-dec > out/q7/$n/listing.txt 2> out/q7/$n/stderr.txt
done
for r in 102837/131072 3/4 11/16 5/8 9/16 168127/262144; do
  n=b$(echo $r | tr / _); mkdir -p out/q7/$n
  sampled out/q7/$n env RAYON_NUM_THREADS=4 timeout 1800 $B executed locks order2 2026093061 8 "b$r=$S/fit8_port.txt@$r" lock-dec > out/q7/$n/listing.txt 2> out/q7/$n/stderr.txt
done
echo "Q7 done $(stamp)" >> out/queue2.log
echo "queue done $(stamp)" >> out/queue2.log
