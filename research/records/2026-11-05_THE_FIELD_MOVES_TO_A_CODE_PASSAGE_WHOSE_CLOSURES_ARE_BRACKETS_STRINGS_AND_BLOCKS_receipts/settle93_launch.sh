#!/bin/bash
# Refinement until each answer settles (Field::release with SETTLE: a problem leaves at the first pass whose held letters are
# at least as likely as its draws on that pass's faces), under both writer laws, in runs, on code86's segment-3 state and
# b1's segment-2 state, the same 32 held and keys as their three-pass writes (closing92, closing91). Fixed before the read
# (the unified-theory reading of 23:26): (a) fences, brackets and strings within half of held's closure, near and far, and
# the code per byte falling, then flat; (b) the median stop past pass 3; (c) of code86's openings not exactly ```python, those
# a byte off stay so at the stop, at most one mending. Projection: a three-pass write 82 to 85 s measured; settling unmeasured,
# outer 1,200 s each (the time guard 1,100 s). Between the card's steps under the lock.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-05-settle93; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# settle93 lock taken $(date -u +%H:%M:%S)"
write() { # NAME STATE THREE_PASS_DIR
  rm -rf $O/$1
  FIELD_WRITER_RUN_BITS=1 $M $1 timeout 1200 $BIN train complete-language length-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 settle 1100000 $O/$1 > $O/$1.log 2>&1
  echo "== $1 on $(sha $2)"; grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$1.log | cut -c1-200
  python3 -I $O/settle.py $P/HELD128.txt $O/$1 $3
  python3 -I $O/endings.py $P/HELD128.txt $O/$1/SAMPLE.tsv 2062
  python3 -I $O/collapse.py $P/HELD128.txt $O/$1/SAMPLE.tsv | head -1
  python3 -I $O/code_reading.py $P/HELD128.txt $O/$1/SAMPLE.tsv | sed -n 2p
  echo "-- closure, settled"; python3 -I $O/code_closure.py $P/HELD128.txt $O/$1/SAMPLE.tsv
  echo "-- closure, three passes"; python3 -I $O/code_closure.py $P/HELD128.txt $3/SAMPLE.tsv
}
write code86_settle $R/2026-11-05-code86/seg3/STATE.4 $R/2026-11-05-closing92/both_refine3
write b1_settle $R/2026-11-05-code87/seg2/STATE.1 $R/2026-11-05-closing91/both_refine3
echo "SETTLE93 exit $(date -u +%H:%M:%S)"
