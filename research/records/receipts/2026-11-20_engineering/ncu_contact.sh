#!/bin/bash
# Nsight Compute on the merged build's contact kernels (field_contact_rows, field_contact_l4, field_contact_columns, field_pace_skin_back): the
# speed-of-light and memory sections of one launch each, after 40 launches of warm-up, on the line's first sections from Y70's end, under the
# card's lock. A reading; no state. Projection: under 5 minutes; timeout 900 s.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/ncu2; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
BIN=$W/tc/bin5/athena; NCU=/opt/cuda-12.9/bin/ncu
sha() { sha256sum "$1" | cut -c1-64; }
src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# ncu: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  for k in field_contact_rows field_contact_l4 field_contact_columns field_pace_skin_back; do
    rm -rf $O/out_$k
    env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin timeout 900 $NCU --kernel-name $k --launch-skip 40 --launch-count 1 --section SpeedOfLight --section MemoryWorkloadAnalysis --section Occupancy --section WarpStateStats \
      $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 6 6 1800000 $O/out_$k $src $(sha $src) > $O/ncu_$k.txt 2>&1
    echo "NCU $k $(date -u +%H:%M:%S) $(grep -E 'Memory Throughput|DRAM Throughput|Compute \(SM\) Throughput|Achieved Occupancy|L1/TEX Hit Rate|L2 Hit Rate|Duration' $O/ncu_$k.txt | sed 's/  */ /g' | tr '\n' ';' | cut -c1-400)"
  done
  echo "# ncu: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "NCU_ALL_DONE $(date -u +%H:%M:%S)"
