#!/bin/bash
# The 64-contact main line at the plain rate, laps ct9-ct12 from ct8 (theory, November 10 20:39: laps stay a lever; both arms' laps go on),
# each as contacts_lap.sh runs a lap. The STOP file in this directory halts the chain before the next lap.
set -u
S=$(ls -t ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/ct8/STATE.* 2>/dev/null | grep -v stopped | head -1)
[ -n "$S" ] || { echo "MAIN no ct8 state"; exit 1; }
for k in 9 10 11 12; do
  [ -e ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/STOP ] && { echo "MAIN STOP read: the chain stops before ct$k"; exit 0; }
  bash ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/contacts_lap.sh $S ct$k || exit 1
  S=$(ls -t ${HOLONICS_ROOT}/.local/wt/qgchgu-sampler/.local/run/2026-11-10-contacts/ct$k/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { echo "MAIN ct$k made no state"; exit 1; }
done
echo "MAIN main laps done $(date -u +%H:%M:%S)"
