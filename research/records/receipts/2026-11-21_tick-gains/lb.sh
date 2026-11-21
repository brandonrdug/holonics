#!/bin/bash
# The contact kernels' register bounds against their occupancy (the register-width item of the engineering report's §11): B, the forward
# contact and the exposure at five blocks a multiprocessor (96 registers, against six's 80 with spills); C, the rows' return at five (96
# registers with more spills, against four's 128). Realizations: the same code, its registers allotted otherwise. Against A, main at
# 6c991fc5c (the paced skins staged). In one hold: each variant's reproduction of 24 sections of L71 from Y70's end; Nsight Compute's duration
# of three launches (after 40) of each changed kernel on each build; then two warmed balanced holds of 40 sections, A against B and A against C.
# Guess (fixed before the hold, the lead, 01:42 UTC): B's forward contact and exposure and C's rows each within 5% of A a launch (occupancy
# gained or lost against spills halved or doubled in a kernel that waits on its loads), and neither section outside the controls' spread.
# Projection: two reproductions of 90 s, six profiles of 30 s, two holds of 9 runs of about 22 s; about 13 minutes; timeouts 600 s a run.
set -u

R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/lb; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt; NCU=/opt/cuda-12.9/bin/ncu
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin "$@"; }
A=$W/sk2/bin_new/athena; B=$O/binB/athena; C=$O/binC/athena; src=$D/arm_Y70/STATE.3000
args() { echo train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $1 $1 1800000 $2 $src $(sha $src); }
( flock -w 14400 9 || exit 75; echo "# lb: lock taken $(date -u +%H:%M:%S) other runs: $(nvidia-smi --query-compute-apps=pid,process_name --format=csv,noheader | tr '\n' ' ')"
  for v in B C; do bin=$B; [ $v = C ] && bin=$C
    rm -rf $O/repro$v; card timeout 600 $bin $(args 24 $O/repro$v) > $O/repro$v.log 2>&1
    echo "LB repro_L71 $v $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro$v.log $D/arm_L71.log 24 --no-save | grep GATE_REPRO | cut -c1-200)"
  done
  for pair in "field_contact_l4 A" "field_contact_l4 B" "field_exposure A" "field_exposure B" "field_contact_rows A" "field_contact_rows C"; do
    set -- $pair; k=$1; v=$2; bin=$A; [ $v = B ] && bin=$B; [ $v = C ] && bin=$C
    rm -rf $O/ncu_${k}_$v; card timeout 900 $NCU --kernel-name $k --launch-skip 40 --launch-count 3 --section SpeedOfLight --section Occupancy $bin $(args 6 $O/ncu_${k}_$v) > $O/ncu_${k}_$v.txt 2>&1
    echo "LB ncu $k $v $(date -u +%H:%M:%S) $(grep -E 'Duration|Achieved Occupancy|Registers Per Thread' $O/ncu_${k}_$v.txt | sed 's/  */ /g' | tr '\n' ';' | cut -c1-360)"
  done
  for v in B C; do bin=$B; [ $v = C ] && bin=$C
    rm -rf $O/ph${v}_w; card timeout 600 $A $(args 40 $O/ph${v}_w) > $O/ph${v}_w.log 2>&1
    echo "LB warm-up $v $(date -u +%H:%M:%S) $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
    k=0
    for b in A $v $v A A $v $v A; do
      k=$((k+1)); run=$A; [ $b != A ] && run=$bin
      rm -rf $O/ph${v}_$k; card FIELD_PHASES=1 timeout 600 $run $(args 40 $O/ph${v}_$k) > $O/ph${v}_$k.log 2>&1
      echo "LB hold $v $k $b $(date -u +%H:%M:%S) $(grep -E '^STORE_SECTION ' $O/ph${v}_$k.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "last30 ms_mean=%.1f", m/c}') $(nvidia-smi --query-gpu=temperature.gpu,clocks.sm --format=csv,noheader)"
    done
  done
  echo "# lb: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "LB_ALL_DONE $(date -u +%H:%M:%S)"
