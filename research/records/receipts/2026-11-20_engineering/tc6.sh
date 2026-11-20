#!/bin/bash
# The site maps on the tensor units, v5 (tc/bin5, merged as #1058), timed against the build before them (dep/bin, the one-pass deposit) in one
# hold of the card with nothing else on it: a warm-up of 40 sections that is not read (tc5's four runs drifted 41 ms between their two controls,
# 523 and 564 ms, with the host idle and the card heating from rest), then control, build, build, control, control, build, build, control, 40
# sections each from Y70's end, the section read over the last 30, the card's temperature and clock beside each run. A timing; no state.
# Guess (fixed before the hold, the lead, 23:01 UTC): the build 20 to 35 ms a section shorter, the controls' own spread under 10 ms once warm.
# Projection: 9 runs of about 25 s, 4 minutes; timeout 600 s a run.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/tc; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
NEW=$O/bin5/athena; OLD=$W/dep/bin/athena; src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# tc6: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  rm -rf $O/ph6_w; card timeout 600 $OLD train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph6_w $src $(sha $src) > $O/ph6_w.log 2>&1
  echo "TC6 warm-up $(date -u +%H:%M:%S) $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  k=0
  for b in old new new old old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph6_$k; card FIELD_PHASES=1 timeout 600 $bin train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph6_$k $src $(sha $src) > $O/ph6_$k.log 2>&1
    echo "TC6 hold $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph6_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  done
  echo "# tc6: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "TC6_ALL_DONE $(date -u +%H:%M:%S)"
