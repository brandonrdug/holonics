#!/usr/bin/env bash
# The batch-sizing fix's checks: parityA5, parityB5, then reading 3's release at A from its STATE.0 (128 held, 16 sweeps, 125 s).
set -u
W=$ROOT/.local/wt/field-card; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; BIN=$W/target/release/examples/field_pass
O=$W/.local/run/fix5; R3=$W/.local/run/reading-3
sha() { sha256sum "$1" | cut -c1-64; }
mkdir -p $O
ok() { grep -q 'FIELD_PARITY_DONE' $W/.local/run/$1.log && ! grep -E 'FIELD_PARITY_DONE' $W/.local/run/$1.log | grep -qE '_unequal=[1-9]'; }
bash $W/.local/run/fp.sh parityA5 420 parity parity-field 32 4 8 2 32 2 16 8 8 1 4 4
ok parityA5 || { echo "STOP parityA5"; exit 1; }
bash $W/.local/run/fp.sh parityB5 540 parity parity-field 32 4 8 2 32 2 16 4 8 2 2 4
ok parityB5 || { echo "STOP parityB5"; exit 1; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 200 > $O/smi.csv &
SMI=$!
rm -rf $O/release
timeout 125 $BIN train complete-language release-field $R3/train/STATE.0 $(sha $R3/train/STATE.0) $R3/train/CODEC $(sha $R3/train/CODEC) $G/UNITS0 $(sha $G/UNITS0) \
  $G/HELD128.txt $(sha $G/HELD128.txt) 128 16 $O/release > $O/release.log 2>&1
echo "RELEASE_END rc=$? $(grep -E 'FIELD_RELEASE |FIELD_CARD|rror' $O/release.log | tr '\n' ' ' | cut -c1-700)"
kill $SMI
echo "BOARD_PEAK_MIB $(sort -n $O/smi.csv | tail -1) baseline=$(head -1 $O/smi.csv)"
for f in FREE.tsv MARKS.tsv COUPLING.tsv; do cmp -s $O/release/$f $R3/release/$f && echo "$f identical" || echo "$f DIFFERS"; done
