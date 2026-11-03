#!/bin/bash
# §16.35's writer read: where the first six held answers' voids fall. (1) run35's lap-20 state written by the open writer of
# §16.27 (every place drawn, the voids dropped), with each place listed; (2) the same state written by the closing writer (a
# drawn void closes the answer); (3) run36's last state by the closing writer. Projection: run35's D 64 write 74 s, a D 128
# write 96 s; each STOP_MS 150,000, outer 170 s; the three under 9 minutes once the card is free (the lock waits for run36,
# whose own deadline ends by 2,930 s from its launch). RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-03-void35
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3300 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
START=$(date +%s)
U="$G/UNITS0 $(sha $G/UNITS0)"
write() { # BIN STATE CODEC NAME
  $M "$4" timeout 170 "$1" train complete-language sample-field "$2" $(sha "$2") "$3" $(sha "$3") $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 150000 $O/$4 > $O/$4.log 2>&1
  grep -E '^FIELD_SAMPLE |^FIELD_SAMPLE_PLACES|^MEASURE' $O/$4.log
}
S35=$W/.local/run/2026-11-03-run35/train/STATE.20; C35=$W/.local/run/2026-11-03-run35/train/CODEC
write $O/field_pass_open "$S35" "$C35" open35
write $O/field_pass_close "$S35" "$C35" close35
S36=$(ls -t $W/.local/run/2026-11-03-run36/train/STATE.* 2>/dev/null | head -1)
[ -n "$S36" ] && write $O/field_pass_close "$S36" $W/.local/run/2026-11-03-run36/train/CODEC close36 && echo "FIELD_RUN state36=$(basename $S36)"
echo "FIELD_RUN exit at_s=$(( $(date +%s) - START ))"
