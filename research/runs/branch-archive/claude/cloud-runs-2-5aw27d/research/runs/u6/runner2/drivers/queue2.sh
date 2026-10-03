#!/usr/bin/env bash
# The second cloud runner's queue (CLOUD_QUEUE.md Q2 control, Q4, Q5, Q7), run in order, each with its peak resident set sampled.
set -u
cd /home/user/holonics
B=target/release/examples/hnn_prediction
B5=.local/wt/run-end/target/release/examples/hnn_prediction
C0=research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state
S=research/runs/u6/states
stamp() { date -u +%FT%TZ; }
sampled() { # <dir> <command…>: run with the peak-RSS sampler, record start, end, exit
  d=$1; shift; mkdir -p $d
  bash out/peak_rss.sh $d/peak_rss.txt & sp=$!
  echo "start $(stamp)" > $d/clock.txt; s=$(date +%s)
  "$@"; rc=$?
  echo "end $(stamp); wall $(( $(date +%s) - s )) s; exit $rc" >> $d/clock.txt
  kill $sp; return $rc
}
heldout() { # <dir> <label>: the held-out read of the chain's final state
  d=$1; lab=$2; fin=$(grep -m1 '^final state' $d/chain.txt | sed 's/^final state //')
  mkdir -p $d; echo "final state $fin" > $d/held_clock.txt
  sampled $d/held_read timeout 5400 $B executed evaluate order2 2026093012 128 $d/held $lab=$fin > $d/held_listing.txt 2> $d/held_stderr.txt
}
echo "Q2k $(stamp)" >> out/queue2.log
mkdir -p out/q2k; sampled out/q2k env METRIC=kinetic UNIT_MS=1900000 DEADLINE_S=1900 RAYON_NUM_THREADS=4 bash research/runs/u6/chain.sh $C0 q2k out/q2k 16 8 0/1 0/1 > out/q2k/chain.txt 2> out/q2k/chain.stderr
heldout out/q2k q2k
echo "Q2k done $(stamp)" >> out/queue2.log
echo "Q4 $(stamp)" >> out/queue2.log
mkdir -p out/q4; sampled out/q4 env METRIC=kinetic-modulus UNIT_MS=1900000 DEADLINE_S=1900 RAYON_NUM_THREADS=4 bash research/runs/u6/chain.sh $S/w3.state q4 out/q4 16 8 0/1 0/1 > out/q4/chain.txt 2> out/q4/chain.stderr
heldout out/q4 q4
echo "Q4 done $(stamp)" >> out/queue2.log
echo "Q5 $(stamp)" >> out/queue2.log
mkdir -p out/q5
sampled out/q5 env RAYON_NUM_THREADS=4 $B5 executed run order2 2026093061 8 out/q5 m13=$S/r13.state lock-dec kinetic 32 ${Q5_DEADLINE_MS:-60800000} > out/q5/listing.txt 2> out/q5/stderr.txt
echo "Q5 done $(stamp)" >> out/queue2.log
echo "Q7 $(stamp)" >> out/queue2.log
mkdir -p out/q7
for s in 0 1/8 1/4 3/8 1/2 5/8 3/4 7/8 1; do
  n=a$(echo $s | tr / _)
  mkdir -p out/q7/$n; sampled out/q7/$n env RAYON_NUM_THREADS=4 timeout 1800 $B executed locks order2 2026093061 8 "a$s=$S/w16.state+$S/fit8_port.txt@102837/131072:$s" lock-dec > out/q7/$n/listing.txt 2> out/q7/$n/stderr.txt
done
for r in 102837/131072 3/4 11/16 5/8 9/16 168127/262144; do
  n=b$(echo $r | tr / _)
  mkdir -p out/q7/$n; sampled out/q7/$n env RAYON_NUM_THREADS=4 timeout 1800 $B executed locks order2 2026093061 8 "b$r=$S/fit8_port.txt@$r" lock-dec > out/q7/$n/listing.txt 2> out/q7/$n/stderr.txt
done
echo "Q7 done $(stamp)" >> out/queue2.log
echo "queue done $(stamp)" >> out/queue2.log
