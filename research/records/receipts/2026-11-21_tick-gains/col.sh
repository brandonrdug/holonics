#!/bin/bash
# The columns' receiver distance and skin entry formed once a receiver (field.cu `field_contact_columns`: the gathering lane forms the pair's
# distance and its skins' support entry and stages them beside the receiver, where every lane of the part had formed them behind the receiver's
# place): a realization, the same integers in the same order. In one hold: the card crate's suite; the reproduction of 24 sections of L71 from
# Y70's end; Nsight Compute's durations of three launches (after 40) of the columns on each build; a warm-up of 40 sections, then the eight-run
# balanced hold against main (dh/bin). It waits for the line's lock between its steps (laps L75 to L78 run).
# Guess (fixed before the hold, the lead, 04:26 UTC): the columns 10 to 25% shorter a launch (the distance's line 16% of its stall samples, the
# support entry's search formed sixteen times a receiver on paced heads); the section 2 to 5 ms shorter.
# Projection: suite 6 to 7 minutes, reproduction 90 s, two profiles of 20 s, hold 9 runs of about 22 s; about 12 minutes once the lock is taken.
set -u

R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/col; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt; NCU=/opt/cuda-12.9/bin/ncu
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
NEW=$O/bin/athena; OLD=$W/dh/bin/athena; src=$D/arm_Y70/STATE.3000
args() { echo train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $1 $1 1800000 $2 $src $(sha $src); }
( flock -w 14400 9 || exit 75; echo "# col: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid,process_name --format=csv,noheader | tr '\n' ' ')"
  ( cd $L/crates/engine-cuda && PATH=/opt/cuda/bin:$PATH timeout 2400 $O/suite_tests --include-ignored --test-threads=1 2>&1 | grep -E "^test |test result|panicked|failures:" | cut -c1-300 > $O/suite.log )
  echo "COL suite $(date -u +%H:%M:%S) $(grep 'test result' $O/suite.log | cut -c1-120) $(grep -E 'FAILED|panicked' $O/suite.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
  rm -rf $O/repro; card timeout 600 $NEW $(args 24 $O/repro) > $O/repro.log 2>&1
  echo "COL repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  for k in field_contact_columns; do for b in old new; do bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ncu_${k}_$b; card timeout 900 $NCU --kernel-name $k --launch-skip 40 --launch-count 3 --section SpeedOfLight $bin $(args 6 $O/ncu_${k}_$b) > $O/ncu_${k}_$b.txt 2>&1
    echo "COL ncu $k $b $(date -u +%H:%M:%S) $(grep -E 'Duration|DRAM Throughput' $O/ncu_${k}_$b.txt | sed 's/  */ /g' | tr '\n' ';' | cut -c1-300)"
  done; done
  rm -rf $O/ph_w; card timeout 600 $OLD $(args 40 $O/ph_w) > $O/ph_w.log 2>&1
  echo "COL warm-up $(date -u +%H:%M:%S) $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  k=0
  for b in old new new old old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph_$k; card FIELD_PHASES=1 timeout 600 $bin $(args 40 $O/ph_$k) > $O/ph_$k.log 2>&1
    echo "COL hold $k $b $(date -u +%H:%M:%S) $(grep -o 'batches=[0-9]*' $O/ph_$k.log | tail -n 1) $(grep -E '^STORE_SECTION ' $O/ph_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  done
  echo "# col: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "COL_ALL_DONE $(date -u +%H:%M:%S)"
