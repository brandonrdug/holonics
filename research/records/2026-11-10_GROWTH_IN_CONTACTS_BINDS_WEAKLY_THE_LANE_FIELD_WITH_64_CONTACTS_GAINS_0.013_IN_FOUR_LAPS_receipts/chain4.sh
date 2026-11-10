#!/bin/bash
# chain4.sh FROM: grow FROM's contacts (grow.sh) and run four grown laps (contacts_lap.sh), laps ct1..ct4, one after another; the STOP file in this
# directory halts the chain before the next stage. Each stage takes the card lock on its own. Launch in the background:
#   nohup bash chain4.sh $R/2026-11-09-nov6-field-resumes/lapNN/STATE.0 > chain4.out 2>&1 &
set -u
N=${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts
[ $# -eq 1 ] || { echo "chain4.sh FROM"; exit 2; }
bash $N/grow.sh $1 $N/g0 || exit 1
S=$N/g0/STATE.0
for k in 1 2 3 4; do
  [ -e $N/STOP ] && { echo "MAIN STOP read: the chain stops before ct$k"; exit 0; }
  bash $N/contacts_lap.sh $S ct$k || exit 1
  S=$(ls -t $N/ct$k/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "MAIN ct$k made no state"; exit 1; }
done
echo "MAIN chain4 done"
