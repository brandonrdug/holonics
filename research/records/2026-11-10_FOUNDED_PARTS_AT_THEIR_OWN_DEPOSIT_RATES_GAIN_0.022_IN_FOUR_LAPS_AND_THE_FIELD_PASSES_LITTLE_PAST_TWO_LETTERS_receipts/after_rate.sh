#!/bin/bash
# After the part-rate arm's rt4: its held locked visit (theory's gauge, 19:40), then its laps rt5-rt8 (theory, 20:39: both arms' laps go
# on), each as chain_rate.sh runs a lap: rate_lap.sh from the last lap's NAME.next, the update reading the two states before and the new one.
set -u
until grep -q "^MAIN rate chain done" ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/contacts-rate.out 2>/dev/null || grep -q "^RUN_EXIT" ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/contacts-rate.out 2>/dev/null; do sleep 60; done
st() { ls -t ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/$1/STATE.* 2>/dev/null | grep -v stopped | head -1; }
S4=$(st rt4); S3=$(st rt3)
[ -n "$S4" ] && [ -n "$S3" ] && [ -f ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/rt4.next ] || { echo "MAIN no rt3, rt4 or rt4.next"; exit 1; }
bash ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/visit_held.sh $S4 rt4
FROM=${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/rt4.next; P2=$S3; P1=$S4
for k in 5 6 7 8; do
  [ -e ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/STOP.rate ] && { echo "MAIN STOP.rate read: the chain stops before rt$k"; exit 0; }
  bash ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/rate_lap.sh $FROM rt$k $P2 $P1 || exit 1
  S=$(st rt$k)
  [ -n "$S" ] && [ -f ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/rt$k.next ] || { echo "MAIN rt$k made no state or rates"; exit 1; }
  P2=$P1; P1=$S; FROM=${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/rt$k.next
done
echo "MAIN rate chain 2 done $(date -u +%H:%M:%S)"
