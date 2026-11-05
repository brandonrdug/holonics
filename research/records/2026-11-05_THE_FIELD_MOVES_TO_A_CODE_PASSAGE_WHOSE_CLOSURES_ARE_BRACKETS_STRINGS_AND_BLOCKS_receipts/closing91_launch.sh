#!/bin/bash
# The writer's two laws (the unified-theory reading of November 5, 22:38) on b1's segment-2 state (code87 seg2 STATE.1), the
# same 32 held and keys as its writes, in runs below a bit: the closing law (a place before the last written letter draws from
# its letters) with the whole room and no refine pass; both laws (and the writer's region ending NEAR past its lowest void)
# with no refine pass; both laws with three. Fixed before the read: the closing law, no refine: written/held 0.7 to 1.4, hazard
# ratio at least 1.5, correlation above +0.3 (only written/held passing: the front hears only the prior); both laws, refine 3:
# top byte under 20%, entropy within 0.5 bits of held, at least 10 of 32 opening with ```python (a collapse with the cut puts
# the fault in refine's two-sided states). Projection: a write in runs 35 to 71 s measured (outer 600 s each). Between
# code87's steps under the lock.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-05-closing91; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; S=$R/2026-11-05-code87/seg2/STATE.1
exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# closing91 lock taken $(date -u +%H:%M:%S) on $(sha $S)"
write() { # NAME ROOM REFINE
  rm -rf $O/$1
  if [ "$2" = 1 ]; then export FIELD_WRITER_ROOM=1; else unset FIELD_WRITER_ROOM; fi
  FIELD_WRITER_RUN_BITS=1 $M $1 timeout 600 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 $3 3000000 $O/$1 > $O/$1.log 2>&1
  echo "== $1 room=$2 refine=$3"; grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/$1.log | cut -c1-200
  python3 -I $O/endings.py $P/HELD128.txt $O/$1/SAMPLE.tsv 2062
  python3 -I $O/collapse.py $P/HELD128.txt $O/$1/SAMPLE.tsv | head -1
  python3 -I $O/unwrote.py $O/$1
  python3 -I $O/code_reading.py $P/HELD128.txt $O/$1/SAMPLE.tsv | sed -n 2p
}
write closing_room_refine0 1 0
write both_refine0 0 0
write both_refine3 0 3
echo "CLOSING91 exit $(date -u +%H:%M:%S)"
