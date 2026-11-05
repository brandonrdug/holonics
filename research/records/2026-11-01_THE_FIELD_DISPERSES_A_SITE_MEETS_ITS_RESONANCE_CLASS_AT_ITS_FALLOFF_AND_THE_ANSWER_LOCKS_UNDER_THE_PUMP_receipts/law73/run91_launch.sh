#!/bin/bash
# A read releases a run (§16.47, the unified-theory readings of November 5, 17:41 and 18:14): the same 32 held GSM8K problems
# on path75's segment 2 state, the same keys (the state's hash), 1,229 sweeps and three refine passes, written once a place a
# read and once in runs bounded strictly below one bit past each run's first place (FIELD_WRITER_RUN_BITS=1), on the tiled
# affine map. Prediction (that reading): reads per write fall at least 1.5 times. Rule: the writes coincide until a run's
# loss first moves a draw; the law stands if the closures (written calculations that close, final lines at the boundary)
# and the length stay within their binomial spread at 32; one past it means the released faces heard each other beyond the
# bound, the open faces are not the marginals training should make, and the blank's face is next.
# Projection: the one-place write measured 1,491 s (path75's segment 2) before the tiled map, outer 2,700 s; the run write at
# most as long. RTX 4080 SUPER under .local/gpu.lock (waited on up to 7,200 s), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-run91; BIN=$O/field_pass; S=$R/2026-11-05-path75/seg2/STATE.2; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "RUN91 LOCK_BUSY"; exit 75; }
echo "# run91 binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
for law in one run; do
  bits=0; [ $law = run ] && bits=1
  rm -rf $O/$law
  FIELD_WRITER_RUN_BITS=$bits $M $law timeout 2700 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 3 2400000 $O/$law > $O/$law.log 2>&1
  echo "== $law $(grep -E '^FIELD_LENGTH|^FIELD_CARD |^MEASURE|rror|panic' $O/$law.log | tr '\n' ' ' | cut -c1-400)"
done
exec 9>&-
for law in one run; do
  echo "== $law"
  python3 -I $O/length.py $O/$law | sed -n '/^end/,/^RULE/p' | head -3
  python3 -I $O/carried.py $G/HELD128.txt $O/$law/SAMPLE.tsv | head -1
  python3 -I $O/endings.py $G/HELD128.txt $O/$law/SAMPLE.tsv | head -1
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/$law/SAMPLE.tsv
done
python3 -I - $O/one/SAMPLE.tsv $O/run/SAMPLE.tsv <<'PY'
import sys
a = [l.split("\t", 1)[1] for l in open(sys.argv[1]) if "\t" in l]
b = [l.split("\t", 1)[1] for l in open(sys.argv[2]) if "\t" in l]
print(f"answers equal under both laws: {sum(x == y for x, y in zip(a, b))} of {len(a)}")
PY
echo "RUN91 exit $(date -u +%H:%M:%S)"
