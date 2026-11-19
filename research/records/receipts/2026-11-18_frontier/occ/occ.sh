#!/bin/bash
# The maps' narrow sums on the int8 tensor cores (MAP_OCC), a realization: every bit kept. Before the
# line trains on it: (1) 24 sections of lap L45 from lap L44's end reproduced against the lap's own log; (2) parity on 3 sections from the
# same state (card against host); (3) one hold of the card lock, a warm-up of 20 sections, then 60 sections each in the order control,
# build, build, control, control, build, build, control (control: pgam/bin/athena_pgam, the line's). No guess: a gate and a timing.
set -u
R=/home/b/Workspaces/holonics; L=$R/.local/wt/lead; D=$L/.local/run/front; O=$L/.local/run/occ; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
NEW=$O/bin/athena_occ; OLD=$L/.local/run/pgam/bin/athena_pgam
from=$D/arm_L44/STATE.3000
sha() { sha256sum "$1" | cut -c1-64; }
card() { env -i HOME=$HOME PATH=/opt/cuda/bin:$PATH "$@"; }
train() { # train BIN OUT SECTIONS
  card timeout 900 $1 train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) $3 $3 1800000 $2 $from $(sha $from) > $2.log 2>&1
}
( flock -w 14400 9 || exit 75; echo "# gate: lock taken $(date -u +%H:%M:%S)"
  rm -rf $O/repro $O/parity
  train $NEW $O/repro 24
  card timeout 2400 $NEW parity complete-language parity-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 3 3 1800000 $O/parity $from $(sha $from) > $O/parity.log 2>&1
  echo "# gate: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "OCC_REPRO $(date -u +%H:%M:%S) $(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L45.log 24 --no-save | grep GATE_REPRO | cut -c1-120) $(grep -h '^FIELD_CARD_OPEN' $O/repro.log | cut -c1-160)"
echo "OCC_PARITY $(grep -h '^STORE_PARITY_DONE' $O/parity.log | cut -c1-140)"
grep -q "equal=24 EQUAL" <(python3 -I $L/tools/reproduction.py $O/repro.log $D/arm_L45.log 24 --no-save) && grep -q "^STORE_PARITY_DONE .* EQUAL$" $O/parity.log || { echo "OCC STOP the build does not keep the line's bits"; exit 1; }
( flock -w 14400 9 || exit 75; echo "# hold: lock taken $(date -u +%H:%M:%S) $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l) other runs on the card"
  rm -rf $O/t_*; train $OLD $O/t_warm 20
  i=0; for b in OLD NEW NEW OLD OLD NEW NEW OLD; do i=$((i+1)); rm -rf $O/t_$i; if [ $b = NEW ]; then train $NEW $O/t_$i 60; else train $OLD $O/t_$i 60; fi
    echo "OCC_TIME run=$i build=$b $(grep '^STORE_SECTION ' $O/t_$i.log | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "sections=%d ms_mean=%.1f", c, m/c}') $(grep -h '^FIELD_CARD ' $O/t_$i.log | grep -o 'batches=[0-9]* peak_store=[0-9]*')"
  done
  echo "# hold: released $(date -u +%H:%M:%S)" ) 9>$LOCK
echo "OCC_ALL_DONE $(date -u +%H:%M:%S)"
