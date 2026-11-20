#!/bin/bash
# The host's parts of a section (the engineering report's items 4 and 18): 40 sections under FIELD_PHASES, whose STORE_DEPOSIT_PARTS and STORE_HOST lines time the deposit's and the host's parts (a reading, every bit kept). Nsight Systems (/opt/cuda-12.9/bin/nsys) traces 40
# sections of train-store from the line's Y70 end (width 224, pumped; the build lanebin/athena at 657099e79) under the card's lock between the
# line's steps; the trace's kernels and copies are joined as intervals and their union is set against the wall from the 11th section's first
# launch to the 40th's last. A reading: no state is kept, nothing enters the line. Projection: 40 sections at 532 to 717 ms plus the trace's
# own cost, under 2 minutes; timeout 600 s.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/eng; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
BIN=$W/lanebin/athena; NSYS=/opt/cuda-12.9/bin/nsys
sha() { sha256sum "$1" | cut -c1-64; }
src=$D/arm_Y70/STATE.3000
rm -rf $O/phases_out
( flock -w 14400 9 || exit 75; echo "# phases: lock taken $(date -u +%H:%M:%S)"
  env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin FIELD_PHASES=1 timeout 600 $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/phases_out $src $(sha $src) > $O/phases_run.log 2>&1
  echo "# phases: exit $? released $(date -u +%H:%M:%S)" ) 9>$LOCK
grep -E '^STORE_DEPOSIT_PARTS|^STORE_HOST|^FIELD_PHASE' $O/phases_run.log | cut -c1-900
grep -E '^STORE_SECTION ' $O/phases_run.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "PHASES_SECTIONS last30 ms_mean=%.1f\n", m/c}'
echo "PHASES_ALL_DONE $(date -u +%H:%M:%S)"
