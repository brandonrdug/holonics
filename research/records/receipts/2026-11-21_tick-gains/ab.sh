#!/bin/bash
# The contacts' operands `a` and `b` kept on 32 bits (field.cu `pa`, `pb`, written by `field_affine_tiled_tc_x32_o32` through `fit32`): a
# realization, every bit kept where every word fits. In one hold: the card crate's suite; the reproduction of 24 sections of L71 from Y70's end;
# Nsight Compute's durations of three launches (after 40) of five kernels that read them, on each build; a warm-up of 40 sections, then the
# eight-run balanced hold against main (dh/bin, the circles' reverse pair part on 64 bits).
# Guess (fixed before the hold, the lead, 03:36 UTC): the circles' face and the pre-scan each 5 to 20% shorter a launch (DRAM-bound at 87 to 88%,
# `a` 8 of their octets a circle and site falling to 4), the gate's return and the pair's return 3 to 15%; the section 2 to 6 ms shorter; three
# batches a section.
# Projection: suite 6 to 7 minutes, reproduction 90 s, ten profiles of 20 s, hold 9 runs of about 22 s; about 15 minutes; timeouts 2400 and 600 s.
set -u

R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/ab; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt; NCU=/opt/cuda-12.9/bin/ncu
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
NEW=$O/bin/athena; OLD=$W/dh/bin/athena; src=$D/arm_Y70/STATE.3000
args() { echo train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $1 $1 1800000 $2 $src $(sha $src); }
( flock -w 14400 9 || exit 75; echo "# ab: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid,process_name --format=csv,noheader | tr '\n' ' ')"
  ( cd $L/crates/engine-cuda && PATH=/opt/cuda/bin:$PATH timeout 2400 $O/suite_tests --include-ignored --test-threads=1 2>&1 | grep -E "^test |test result|panicked|failures:" | cut -c1-300 > $O/suite.log )
  echo "AB suite $(date -u +%H:%M:%S) $(grep 'test result' $O/suite.log | cut -c1-120) $(grep -E 'FAILED|panicked' $O/suite.log | head -n 2 | tr '\n' ' ' | cut -c1-200)"
  rm -rf $O/repro; card timeout 600 $NEW $(args 24 $O/repro) > $O/repro.log 2>&1
  echo "AB repro_L71 $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  for k in field_pair_scan_face field_pair_scan_pre field_pair_gate_back field_pair_gamma field_pair_back; do for b in old new; do bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ncu_${k}_$b; card timeout 900 $NCU --kernel-name $k --launch-skip 40 --launch-count 3 --section SpeedOfLight $bin $(args 6 $O/ncu_${k}_$b) > $O/ncu_${k}_$b.txt 2>&1
    echo "AB ncu $k $b $(date -u +%H:%M:%S) $(grep -E 'Duration|DRAM Throughput' $O/ncu_${k}_$b.txt | sed 's/  */ /g' | tr '\n' ';' | cut -c1-300)"
  done; done
  rm -rf $O/ph_w; card timeout 600 $OLD $(args 40 $O/ph_w) > $O/ph_w.log 2>&1
  echo "AB warm-up $(date -u +%H:%M:%S) $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  k=0
  for b in old new new old old new new old; do
    k=$((k+1)); bin=$OLD; [ $b = new ] && bin=$NEW
    rm -rf $O/ph_$k; card FIELD_PHASES=1 timeout 600 $bin $(args 40 $O/ph_$k) > $O/ph_$k.log 2>&1
    echo "AB hold $k $b $(date -u +%H:%M:%S) $(grep -o 'batches=[0-9]*' $O/ph_$k.log | tail -n 1) $(grep -E '^STORE_SECTION ' $O/ph_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
  done
  echo "# ab: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "AB_ALL_DONE $(date -u +%H:%M:%S)"
