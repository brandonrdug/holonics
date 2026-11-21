#!/bin/bash
# Nsight Compute source counters on the contact kernels of a line-info build (the merged tree at e63c81396 with -lineinfo, every bit the
# same), one launch each after 40 of warm-up, on the line's first sections from Y70's end, under the card's lock. A reading; no state.
# Projection: under 6 minutes; timeout 900 s a kernel.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/ncu_src; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
BIN=$W/li_athena; NCU=/opt/cuda-12.9/bin/ncu
sha() { sha256sum "$1" | cut -c1-64; }
src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# ncu: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  for k in "$@"; do
    rm -rf $O/out_$k
    env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin timeout 900 $NCU --kernel-name $k --launch-skip 40 --launch-count 1 --section SourceCounters --section WarpStateStats --section LaunchStats --section Occupancy --section SpeedOfLight --import-source yes -o $O/rep_$k -f \
      $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 6 6 1800000 $O/out_$k $src $(sha $src) > $O/ncu_$k.txt 2>&1
    echo "NCU $k $(date -u +%H:%M:%S) exit=$?"
  done
  echo "# ncu: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "NCU_ALL_DONE $(date -u +%H:%M:%S)"
