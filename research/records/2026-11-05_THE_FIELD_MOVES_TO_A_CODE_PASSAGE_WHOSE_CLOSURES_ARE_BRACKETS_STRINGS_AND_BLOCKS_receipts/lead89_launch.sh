#!/bin/bash
# The held opening's leading bytes on code86's segment-3 state, the first 32 held problems (the write's), read as the writer
# meets them (the unified-theory reading of November 5, 22:02). A reading of about 4 card-seconds (outer 300 s), between
# code87's steps under the lock.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-05-lead89; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; S=$R/2026-11-05-code86/seg3/STATE.4
exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lead89 lock taken $(date -u +%H:%M:%S)"
rm -rf $O/held
$M held timeout 300 $BIN train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $P/TRAIN.txt $(sha $P/TRAIN.txt) 32 $O/held > $O/held.log 2>&1
exec 9>&-
grep -E '^FIELD_OPENING|^MEASURE|rror|panic' $O/held.log | cut -c1-200
python3 -I $O/lead.py $O/held 32
echo "LEAD89 exit $(date -u +%H:%M:%S)"
