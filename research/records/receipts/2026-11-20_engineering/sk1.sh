#!/bin/bash
# The paced skins' return spread over entry and mode lanes (field.cu `field_pace_skin_back`): a realization, every bit kept. In one hold of the
# card with nothing else on it: the card crate's suite (every parity of card against host); the reproduction of 24 sections of lap L71 from
# Y70's end (tools/reproduction.py); a warm-up of 40 sections not read, then the eight-run balanced hold against the merged build (tc/bin5).
# Guess (fixed before the hold, the lead, 23:12 UTC): the section 5 to 12 ms shorter (the kernel 15 ms a section at 6.09 active lanes of 32).
# Projection: suite 6 to 7 minutes, reproduction 90 s, hold 9 runs of about 25 s; about 12 minutes; timeouts 2400 and 600 s.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/sk; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
NEW=$O/bin/athena; OLD=$W/tc/bin5/athena; src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75; echo "# sk1: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l)"
  ( cd $L/crates/engine-cuda && PATH=/opt/cuda/bin:$PATH timeout 2400 $O/suite_tests --include-ignored --test-threads=1 2>&1 | grep -E "^test |test result|panicked|failures:" | cut -c1-300 > $O/suite.log )
  echo "SK1 suite $(date -u +%H:%M:%S) $(grep 'test result' $O/suite.log | cut -c1-120) $(grep -E 'FAILED|panicked' $O/suite.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
  rm -rf $O/repro; card timeout 600 $NEW train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 24 24 1800000 $O/repro $src $(sha $src) > $O/repro.log 2>&1
  echo "SK1 repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  rm -rf $O/ph_w; card timeout 600 $OLD train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph_w $src $(sha $src) > $O/ph_w.log 2>&1
  echo "SK1 warm-up $(date -u +%H:%M:%S) $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  k=0
  for b in old new new old old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph_$k; card FIELD_PHASES=1 timeout 600 $bin train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/ph_$k $src $(sha $src) > $O/ph_$k.log 2>&1
    echo "SK1 hold $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  done
  echo "# sk1: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "SK1_ALL_DONE $(date -u +%H:%M:%S)"
