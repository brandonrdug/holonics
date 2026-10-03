#!/usr/bin/env bash
cd /home/user/holonics
until [ -s out/q3/progress.txt ]; do sleep 10; done
C0=research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state
t0=$(date +%s)
RAYON_NUM_THREADS=2 timeout 1800 .local/target-q10/release/examples/hnn_prediction executed kinetic-coupling order2 2026093061 8 lock-dec c0=$C0 > out/q11/kinetic-coupling.txt 2>&1
echo "q11 exit $? wall $(( $(date +%s)-t0 )) s"
