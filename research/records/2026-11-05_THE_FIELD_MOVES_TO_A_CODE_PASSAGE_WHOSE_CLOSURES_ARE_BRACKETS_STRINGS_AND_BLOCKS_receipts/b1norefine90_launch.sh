#!/bin/bash
# b1's two-lap state (code87 seg2 STATE.1) written in runs with no refine pass, beside code87's own write (runs, three refine
# passes): collapse88 put code86's collapse in the refine passes, so b1's length and content are read on its sweeps too.
# A write in runs about 35 s measured (outer 600 s), between code87's steps under the lock.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-05-b1norefine90; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; S=$R/2026-11-05-code87/seg2/STATE.1
exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# b1norefine90 lock taken $(date -u +%H:%M:%S) on $(sha $S)"
rm -rf $O/write
FIELD_WRITER_RUN_BITS=1 $M write timeout 600 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/write > $O/write.log 2>&1
exec 9>&-
grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/write.log | cut -c1-200
python3 -I $O/endings.py $P/HELD128.txt $O/write/SAMPLE.tsv 2062
python3 -I $O/collapse.py $P/HELD128.txt $O/write/SAMPLE.tsv
python3 -I $O/code_reading.py $P/HELD128.txt $O/write/SAMPLE.tsv
python3 -I $O/code_closure.py $P/HELD128.txt $O/write/SAMPLE.tsv
echo "B1NOREFINE90 exit $(date -u +%H:%M:%S)"
