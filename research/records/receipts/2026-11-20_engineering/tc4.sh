#!/bin/bash
# Gate 3 of the tensor-core site maps (v5): the card crate's suite alone under the card lock, every parity of card against host. Projection:
# 6 to 7 minutes (368 s at 20:46); timeout 2400 s.
set -u
R=$REPO; L=$R/.local/wt/lead; O=$L/.local/run/tc; LOCK=$R/.local/gpu.lock
( flock -w 14400 9 || exit 75; echo "# tc4: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  cd $L/crates/engine-cuda && PATH=/opt/cuda/bin:$PATH timeout 2400 $O/bench_tests5 --include-ignored --test-threads=1 2>&1 | grep -E "^test |test result|panicked|failures:" | cut -c1-300 > $O/suite5.log
  echo "TC4 suite $(date -u +%H:%M:%S) $(grep 'test result' $O/suite5.log | cut -c1-120) $(grep -E 'FAILED|panicked' $O/suite5.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
  echo "# tc4: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "TC4_ALL_DONE $(date -u +%H:%M:%S)"
