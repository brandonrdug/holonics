#!/bin/bash
# chain_rate.sh [FROM]: the founded parts' deposit rates, four laps rt1-rt4 from ct4's state (theory, November 10 19:05): open the parts' rates on
# FROM (default ct4/STATE.0: the contact set's three parts and the lane's E, E-, E+ (enc, before, after) at three octaves, 2^-9; every other part at
# 2^-12), then rate_lap.sh for each lap, each lap's NAME.next carrying the rates to the next. The update after lap rtk reads rt(k-2), rt(k-1) and rtk
# (rt1: ct3, ct4 and rt1). The STOP.rate file in this directory halts the chain before the next lap. A RATE_ALARM line is printed where a lap ends
# above the one before on the held joint, and the chain goes on. Launch in the background (nohup bash chain_rate.sh > chain_rate.out 2>&1 &),
# when the main line's stages are underway; the control is ct5-ct8.
set -u
N=${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts
sha() { sha256sum "$1" | cut -c1-64; }
S4=${1:-$(ls -t $N/ct4/STATE.* 2>/dev/null | grep -v stopped | head -1)}
S3=$(ls -t $N/ct3/STATE.* 2>/dev/null | grep -v stopped | head -1)
[ -n "$S4" ] && [ -n "$S3" ] || { echo "MAIN no ct3 or ct4 state"; exit 1; }
rm -f $N/rt0.state
python3 -I $N/part_rates.py open $S4 32 3,3,3,3,3,3,0,0,0,0,0,0,0,0,0 $N/rt0.state || { echo "MAIN the opening failed"; exit 1; }
FROM=$N/rt0.state; P2=$S3; P1=$S4
for k in 1 2 3 4; do
  [ -e $N/STOP.rate ] && { echo "MAIN STOP.rate read: the chain stops before rt$k"; exit 0; }
  bash $N/rate_lap.sh $FROM rt$k $P2 $P1 || exit 1
  S=$(ls -t $N/rt$k/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] && [ -f $N/rt$k.next ] || { echo "MAIN rt$k made no state or rates"; exit 1; }
  P2=$P1; P1=$S; FROM=$N/rt$k.next
done
echo "MAIN rate chain done $(date -u +%H:%M:%S)"
