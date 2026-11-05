#!/bin/bash
# The opening's lean on training problems (§16.47, the unified-theory reading of November 5, 11:13): opening-field on
# boundary73 segment 2's last state over the first 128 training problems (the boundary comparison's own optimum puts their
# mean expected length at the opening less the answer's at zero). Projection: 3.6 s (deadline 300 s). RTX 4080 SUPER under
# .local/gpu.lock (a window between the chains' steps), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-train77; BIN=$R/2026-11-05-path75/field_pass; B=$R/2026-11-05-boundary73; S=$(ls -t $B/seg2/STATE.* | grep -v stopped | head -1); CODEC=$B/seg2/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "TRAIN77 LOCK_BUSY"; exit 75; }
echo "# train77 state $(basename $S) lock taken $(date -u +%H:%M:%S)"
for set in TRAIN HELD128; do
  rm -rf $O/$set
  $M $set timeout 300 $BIN train complete-language opening-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/$set.txt $(sha $G/$set.txt) $G/TRAIN.txt $(sha $G/TRAIN.txt) 128 $O/$set > $O/$set.log 2>&1
  echo "== $set $(grep -E '^MEASURE' $O/$set.log | sed 's/.*wall_s=/wall_s=/')"
  python3 -I $R/2026-11-05-path75/opening.py $O/$set | grep -E '^(\+0|-32|\+128|\+512)|^B past|^void mass|expected length less held'
done
exec 9>&-
echo "TRAIN77 exit $(date -u +%H:%M:%S)"
