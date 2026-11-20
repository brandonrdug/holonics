#!/bin/bash
# The site maps on the tensor units, v5 (v4 with every output written in place: the forward map reads the sites from digit planes, the transposed map stages the covector's digits). In one hold of
# the card after the line's lap L74: the width-224 map bench (the tensor route beside the tile form, outputs compared word for word); the
# reproduction of 24 sections of lap L71 from Y70's end with this build (tools/reproduction.py); one balanced hold of 40 sections each from Y70's
# end (the merged build dep/bin, this build, this build, dep/bin) under FIELD_PHASES. Guess (fixed before the hold, the lead, 22:08 UTC; the repeat of tc3, whose hold ran beside gate 1 on the host): the
# section 20 to 35 ms shorter than the merged build's (tc3 read 29 ms with gate 1 beside it; v4 read 18 clean; v5's forward map 479 µs and transposed
# 533 beside the gate). Projection: bench 5 s, reproduction 90 s, hold 4 × 25 s; about 4 minutes; timeouts 300 and 600 s.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/tc; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
NEW=$O/bin5/athena; OLD=$W/dep/bin/athena; src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# tc3b: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  ( cd $L/crates/engine-cuda && FIELD_MAPS_LAUNCHES=60 PATH=/opt/cuda/bin:$PATH timeout 300 $O/bench_tests5 --include-ignored --test-threads=1 --nocapture the_site_maps_at_width_224 2>&1 | grep -E 'MAPS224|panicked|test result' )
  rm -rf $O/repro5b; card timeout 600 $NEW train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 24 24 1800000 $O/repro5b $src $(sha $src) > $O/repro5b.log 2>&1
  echo "TC5 repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro5b.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  k=0
  for b in old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph5b_$k; card FIELD_PHASES=1 timeout 600 $bin train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph5b_$k $src $(sha $src) > $O/ph5b_$k.log 2>&1
    echo "TC5 hold $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph5b_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(grep -E '^FIELD_CARD ' $O/ph5b_$k.log | grep -o 'return_ms=[0-9]*')"
  done
  echo "# tc3b: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "TC5_ALL_DONE $(date -u +%H:%M:%S)"
