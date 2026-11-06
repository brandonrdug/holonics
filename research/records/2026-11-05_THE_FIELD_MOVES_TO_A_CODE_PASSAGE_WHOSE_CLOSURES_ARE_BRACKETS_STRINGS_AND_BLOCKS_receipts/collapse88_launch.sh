#!/bin/bash
# Where code86's collapse is made (the unified-theory reading of November 5, 21:54: stray 'y's starting inside the region in
# more than four writes put the cause in the writer's own loop; on code86's write 30 of 32 start at places 0 to 5). The same
# state (code86 seg3 STATE.4), the same 32 held and keys, three writes beside the recorded one (runs below a bit, three refine
# passes): runs with no refine pass, one place a read with three, and one place a read with none. collapse.py reads each.
# Projection: a write in runs 49 s measured, one place a read about 674 s (code84's segment 2); the outer stops 600 s and
# 1,500 s. It takes the card between code87's steps (the lock serializes them; code87 waits up to 7,200 s).
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-05-collapse88; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; S=$R/2026-11-05-code86/seg3/STATE.4
exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# collapse88 lock taken $(date -u +%H:%M:%S) on $(sha $S)"
write() { # NAME RUN_BITS REFINE OUTER
  rm -rf $O/$1
  if [ "$2" = 1 ]; then export FIELD_WRITER_RUN_BITS=1; else unset FIELD_WRITER_RUN_BITS; fi
  $M $1 timeout $4 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 $3 3000000 $O/$1 > $O/$1.log 2>&1
  echo "== $1 runs=$2 refine=$3"; grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$1.log | cut -c1-200
  python3 -I $O/collapse.py $P/HELD128.txt $O/$1/SAMPLE.tsv | head -1
}
write runs_refine0 1 0 600
write one_refine3 0 3 1500
write one_refine0 0 0 1500
echo "COLLAPSE88 exit $(date -u +%H:%M:%S)"
