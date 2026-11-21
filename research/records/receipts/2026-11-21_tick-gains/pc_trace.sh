#!/bin/bash
# Per-kernel time of the two builds of pc.sh (main's kernels, nq/bin; the pair's face on 32 bits, pc/bin) under Nsight Systems, 20 sections each
# from Y70's end, under the card's lock, to find which kernel moved the section 7 ms the slower way. A reading. Projection under 2 minutes each.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/pc; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt; NSYS=/opt/cuda-12.9/bin/nsys
sha() { sha256sum "$1" | cut -c1-64; }
src=$D/arm_Y70/STATE.3000
( flock -w 14400 9 || exit 75
  for b in old new; do BIN=$W/nq/bin/athena; [ $b = new ] && BIN=$O/bin/athena
    rm -rf $O/tr_$b $O/tr_$b.nsys-rep $O/tr_$b.sqlite
    env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin timeout 600 $NSYS profile --trace=cuda --sample=none --cpuctxsw=none --output=$O/tr_$b --force-overwrite=true \
      $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 20 20 1800000 $O/tr_out_$b $src $(sha $src) > $O/tr_run_$b.log 2>&1
    $NSYS export --type=sqlite --output=$O/tr_$b.sqlite --force-overwrite=true $O/tr_$b.nsys-rep > /dev/null 2>&1
    echo "TR $b $(date -u +%H:%M:%S)"
  done ) 9>$LOCK
