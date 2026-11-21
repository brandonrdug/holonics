#!/bin/bash
# The forward contact's paced skins staged with the chunk's terms (field.cu `contact_body`, `stage_skin_words`): a realization, every bit kept.
# In one hold of the card with nothing else of ours on it: the card crate's suite (every parity of card against host); the reproduction of 24
# sections of lap L71 from Y70's end (tools/reproduction.py); Nsight Compute's duration of one field_contact_l4 launch (after 40) for each build;
# a warm-up of 40 sections not read, then the eight-run balanced hold against the merged build (sk2/bin_ctl, main at 6b9a525fb).
# Guess (fixed before the hold, the lead, 01:25 UTC): field_contact_l4 10 to 18% shorter a launch (the two skin lines held 19.8% of its stall
# samples); the section 1.5 to 3 ms shorter, which may stand inside the controls' spread (then read as no difference at the section).
# Projection: suite 6 to 7 minutes, reproduction 90 s, two profiles of 30 s, hold 9 runs of about 25 s; about 13 minutes; timeouts 2400 and 600 s.
set -u

R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/sk2; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt; NCU=/opt/cuda-12.9/bin/ncu
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
NEW=$O/bin_new/athena; OLD=$O/bin_ctl/athena; src=$D/arm_Y70/STATE.3000
args() { echo train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $1 $1 1800000 $2 $src $(sha $src); }
( flock -w 14400 9 || exit 75; echo "# sk2: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid,process_name --format=csv,noheader | tr '\n' ' ')"
  ( cd $L/crates/engine-cuda && PATH=/opt/cuda/bin:$PATH timeout 2400 $O/suite_tests --include-ignored --test-threads=1 2>&1 | grep -E "^test |test result|panicked|failures:" | cut -c1-300 > $O/suite.log )
  echo "SK2 suite $(date -u +%H:%M:%S) $(grep 'test result' $O/suite.log | cut -c1-120) $(grep -E 'FAILED|panicked' $O/suite.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
  rm -rf $O/repro; card timeout 600 $NEW $(args 24 $O/repro) > $O/repro.log 2>&1
  echo "SK2 repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  for b in old new; do bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ncu_$b; card timeout 900 $NCU --kernel-name field_contact_l4 --launch-skip 40 --launch-count 3 --section SpeedOfLight --section Occupancy $bin $(args 6 $O/ncu_$b) > $O/ncu_$b.txt 2>&1
    echo "SK2 ncu $b $(date -u +%H:%M:%S) $(grep -E 'Duration|Achieved Occupancy' $O/ncu_$b.txt | sed 's/  */ /g' | tr '\n' ';' | cut -c1-300)"
  done
  rm -rf $O/ph_w; card timeout 600 $OLD $(args 40 $O/ph_w) > $O/ph_w.log 2>&1
  echo "SK2 warm-up $(date -u +%H:%M:%S) $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  k=0
  for b in old new new old old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph_$k; card FIELD_PHASES=1 timeout 600 $bin $(args 40 $O/ph_$k) > $O/ph_$k.log 2>&1
    echo "SK2 hold $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  done
  echo "# sk2: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "SK2_ALL_DONE $(date -u +%H:%M:%S)"
