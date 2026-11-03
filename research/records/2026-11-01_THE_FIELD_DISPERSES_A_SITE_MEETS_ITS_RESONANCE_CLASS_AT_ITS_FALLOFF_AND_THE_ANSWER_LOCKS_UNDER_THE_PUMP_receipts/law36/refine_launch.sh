#!/bin/bash
# §16.36's refinement read: run37's last state (or run36's lap 19 if run37 left none) writes the first six held answers once
# and with three refinement passes (FIELD_SAMPLE_REFINE=3), the closing writer in both. Projection: one pass 64 s (run36's
# state, close36), a refinement pass about 70 s (one read a place of the longest answer body, 1,109 places at about 61 ms);
# the single write STOP_MS 150,000, outer 170 s; the refined 64 + 3 x 70 = 274 s, STOP_MS 330,000, outer 350 s. Then the copy
# onset read and the writer's card parity (toy35/onset.sh). RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-03-refine36; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
(
exec 9>$ROOT/.local/gpu.lock
flock -w 5400 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
S=$(ls -t $W/.local/run/2026-11-03-run37/train/STATE.* 2>/dev/null | head -1); C=$W/.local/run/2026-11-03-run37/train/CODEC
[ -n "$S" ] || { S=$W/.local/run/2026-11-03-run36/train/STATE.19; C=$W/.local/run/2026-11-03-run36/train/CODEC; }
echo "FIELD_RUN state=$S"
U="$G/UNITS0 $(sha $G/UNITS0)"
write() { # NAME REFINE STOP OUTER
  FIELD_SAMPLE_REFINE=$2 $M "$1" timeout $4 $BIN train complete-language sample-field "$S" $(sha "$S") "$C" $(sha "$C") $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 $3 $O/$1 > $O/$1.log 2>&1
  grep -E '^FIELD_SAMPLE |^FIELD_SAMPLE_PLACES|^MEASURE' $O/$1.log
  python3 -I $O/words.py $G/TRAIN.txt $O/$1/SAMPLE.tsv
}
write once 0 150000 170
write refined 3 330000 350
)
bash $W/.local/run/toy35/onset.sh > $W/.local/run/toy35/onset.out 2>&1
echo "FIELD_RUN onset done"
