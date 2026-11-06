#!/bin/bash
# The octave law at every byte (the unified-theory reading of November 6, 00:14; FIELD_WRITER_PLACE_ORDER): each octave of
# the sweeps drawn in place order, runs below a bit, both writer laws, no refine pass, on code86's segment-3 state, the same
# 32 held and keys as its keyed writes (closing92). Fixed before the read: (1) far brackets and strings close above the keyed
# three-pass write's 0.24 and 0.16 of held; (2) no opening a byte off (keyed three-pass: 2); (3) entropy within 0.3 of held's
# 4.96, top byte under 20%; (4) exact ```python openings within 3 of the passage's 83.8% (about 27 of 32). Length read apart.
# If (1) to (3) pass, the path law follows the order in training; if content reads worse than the keyed sweeps alone
# (closing92 both_refine0), the faces past a front with a silent right side are the subject. A write in runs about 46 s
# measured (outer 600 s), between the card's steps under the lock.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-06-place94; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; S=$R/2026-11-05-code86/seg3/STATE.4
exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# place94 lock taken $(date -u +%H:%M:%S) on $(sha $S)"
rm -rf $O/place_refine0
FIELD_WRITER_PLACE_ORDER=1 FIELD_WRITER_RUN_BITS=1 $M place_refine0 timeout 600 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/place_refine0 > $O/place_refine0.log 2>&1
exec 9>&-
grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/place_refine0.log | cut -c1-200
for d in place_refine0; do
  python3 -I $O/endings.py $P/HELD128.txt $O/$d/SAMPLE.tsv 2062
  python3 -I $O/collapse.py $P/HELD128.txt $O/$d/SAMPLE.tsv | head -1
  python3 -I $O/code_reading.py $P/HELD128.txt $O/$d/SAMPLE.tsv | sed -n 2p
  python3 -I $O/code_closure.py $P/HELD128.txt $O/$d/SAMPLE.tsv
done
echo "-- the keyed sweeps alone (closing92 both_refine0)"
python3 -I $O/collapse.py $P/HELD128.txt $R/2026-11-05-closing92/both_refine0/SAMPLE.tsv | head -1
python3 -I $O/code_closure.py $P/HELD128.txt $R/2026-11-05-closing92/both_refine0/SAMPLE.tsv
echo "PLACE94 exit $(date -u +%H:%M:%S)"
