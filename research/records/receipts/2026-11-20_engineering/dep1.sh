#!/bin/bash
# The deposit in one pass a family (learner.rs `deposit_pass`, the engineering report's host deposit): a realization, every bit kept. Its receipts:
#   1. the build (athena release) from the lead worktree as it stands;
#   2. gate 3's reproduction on today's line: 24 sections of lap L71 from Y70's end against the lap's own log (tools/reproduction.py), which reads
#      every STORE_SECTION field (the code, the transfer, the external price, the opening) but the timings;
#   3. one balanced hold of the card (control, build, build, control) of 40 sections each from Y70's end under FIELD_PHASES: the deposit's
#      parts (STORE_DEPOSIT_PARTS) and the section's ms over the last 30 sections. The control is lanebin/athena (657099e79), the line's binary.
# A reading and a gate: no state enters the line. Projection: the build 2 to 4 minutes; the reproduction 90 s; each phases run 60 to 80 s, so the
# hold about 6 minutes, behind the line's lap L72 (its lock frees near 20:30). Timeouts: 600 s a run.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/dep; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
cd $L && echo "DEP1 head $(git rev-parse --short=9 HEAD) $(git status --porcelain --untracked-files=no | wc -l) changed files $(date -u +%H:%M:%S)"
PATH=/opt/cuda/bin:$PATH cargo build --release -p athena > $O/build.log 2>&1; b=$?
echo "DEP1 build=$b $(date -u +%H:%M:%S) warnings=$(grep -c '^warning' $O/build.log) $(grep -E '^error' $O/build.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
[ $b -eq 0 ] || { echo "DEP1 STOP the build did not link"; exit 1; }
mkdir -p $O/bin && cp $L/target/release/athena $O/bin/athena
NEW=$O/bin/athena; OLD=$W/lanebin/athena; src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# hold: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  rm -rf $O/repro; card timeout 600 $NEW train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 24 24 1800000 $O/repro $src $(sha $src) > $O/repro.log 2>&1
  echo "DEP1 repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  k=0
  for b in old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph_$k; card FIELD_PHASES=1 timeout 600 $bin train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph_$k $src $(sha $src) > $O/ph_$k.log 2>&1
    echo "DEP1 hold $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}; if(a[1]=="deposit_ms"){d+=a[2]}}} END{printf "last30 ms_mean=%.1f deposit_ms_mean=%.1f", m/c, d/c}') $(grep -E '^STORE_DEPOSIT_PARTS' $O/ph_$k.log | cut -c1-400)"
  done
  echo "# hold: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "DEP1_ALL_DONE $(date -u +%H:%M:%S)"
