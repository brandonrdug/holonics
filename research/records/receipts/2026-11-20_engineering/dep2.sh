#!/bin/bash
# The batches' lists packed one batch ahead on a host thread (resident.rs `stage_lists`, the engineering report's batch edges): a realization,
# every bit kept, on top of the one-pass deposit (dep1). Its receipts:
#   1. the build (athena release, and the card crate's tests) from the lead worktree as it stands;
#   2. the card crate's suite alone under the lock (every parity of card against host);
#   3. gate 3's reproduction on today's line: 24 sections of lap L71 from Y70's end against the lap's own log (tools/reproduction.py);
#   4. one balanced hold (dep1's build, this build, this build, dep1's build) of 40 sections each from Y70's end under FIELD_PHASES.
# A gate and a reading: no state enters the line. Projection: build 2 minutes; suite 6 to 7 minutes (371 s on November 19); reproduction 90 s;
# the hold about 5 minutes. Timeouts: 2400 s the suite, 600 s a run.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/dep; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
cd $L && echo "DEP2 head $(git rev-parse --short=9 HEAD) $(git status --porcelain --untracked-files=no | wc -l) changed files $(date -u +%H:%M:%S)"
PATH=/opt/cuda/bin:$PATH cargo build --release -p athena > $O/build2.log 2>&1; b1=$?
PATH=/opt/cuda/bin:$PATH cargo test --release -p holonics-engine-cuda --no-run > $O/build2_tests.log 2>&1; b2=$?
T=$L/$(grep -o "target/release/deps/holonics_engine_cuda-[0-9a-f]*" $O/build2_tests.log | head -n 1)
echo "DEP2 build athena=$b1 card_tests=$b2 $(date -u +%H:%M:%S) warnings=$(grep -c '^warning' $O/build2.log) $(grep -E '^error' $O/build2.log $O/build2_tests.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
[ $b1 -eq 0 ] && [ $b2 -eq 0 ] && [ -x "$T" ] || { echo "DEP2 STOP the build did not link"; exit 1; }
mkdir -p $O/bin2 && cp $L/target/release/athena $O/bin2/athena
NEW=$O/bin2/athena; OLD=$O/bin/athena; src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# hold2: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  cd $L/crates/engine-cuda && PATH=/opt/cuda/bin:$PATH timeout 2400 $T --include-ignored --test-threads=1 2>&1 | grep -E "^test |test result|panicked|failures:" | cut -c1-300 > $O/suite2.log
  echo "DEP2 suite $(date -u +%H:%M:%S) $(grep 'test result' $O/suite2.log | cut -c1-120) $(grep -E 'FAILED|panicked' $O/suite2.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
  cd $L && rm -rf $O/repro2; card timeout 600 $NEW train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 24 24 1800000 $O/repro2 $src $(sha $src) > $O/repro2.log 2>&1
  echo "DEP2 repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro2.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  k=0
  for b in old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph2_$k; card FIELD_PHASES=1 timeout 600 $bin train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph2_$k $src $(sha $src) > $O/ph2_$k.log 2>&1
    echo "DEP2 hold $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph2_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(grep -E '^FIELD_PHASE name=(stage_lists|outside_the_card) ' $O/ph2_$k.log | tr '\n' ' ' | cut -c1-300)"
  done
  echo "# hold2: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "DEP2_ALL_DONE $(date -u +%H:%M:%S)"
