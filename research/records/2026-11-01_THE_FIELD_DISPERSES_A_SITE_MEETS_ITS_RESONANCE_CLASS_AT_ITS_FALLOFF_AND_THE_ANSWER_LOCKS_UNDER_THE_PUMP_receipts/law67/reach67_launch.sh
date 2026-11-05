#!/bin/bash
# The question's reach into a blank answer (§16.45, the unified-theory reading of November 5): reach-field at the writer's
# first state on main52 seg3's last three states (the old law: a blank at one) and exact63 seg5's last three (the free
# clock: a blank at its expected duration, its face uncompared), each place's duration, its variation from the question and
# its code under its own question and the foil. Reach is the cause if exact63's excess grows with distance and its question
# effect falls below the old law's there. Projection: an unmeasured read, planned at 1 to 3 minutes (restate-field's whole
# read was 60 to 97 s, this reads 3 passes a problem against its 46); deadline 240 s each; stop after the first if it passes
# 150 s. RTX 4080 SUPER under .local/gpu.lock (one window between faces66's steps), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-reach67; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "REACH LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S) old $(sha $O/field_pass_old) law $(sha $O/field_pass_law)"
first=1
for pair in old:$R/2026-11-04-main52/seg3/STATE.10 old:$R/2026-11-04-main52/seg3/STATE.9 old:$R/2026-11-04-main52/seg3/STATE.8 law:$R/2026-11-05-exact63/seg5/STATE.8 law:$R/2026-11-05-exact63/seg5/STATE.7 law:$R/2026-11-05-exact63/seg5/STATE.6; do
  law=${pair%%:*}; ST=${pair#*:}; tag=$law-$(basename $(dirname $(dirname $ST)))-$(basename $(dirname $ST))-$(basename $ST)
  rm -rf $O/$tag
  t0=$(date +%s)
  $M $tag timeout 240 $O/field_pass_$law train complete-language reach-field $ST $(sha $ST) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 $O/$tag > $O/$tag.log 2>&1
  echo "$tag $(grep -E '^FIELD_REACH_DONE' $O/$tag.log) $(grep -E '^MEASURE' $O/$tag.log | sed 's/.*wall_s=/wall_s=/')"; grep -E 'rror|panic' $O/$tag.log | head -3
  if [ $first = 1 ] && [ $(( $(date +%s) - t0 )) -gt 150 ]; then echo "REACH stopped: the first read passed 150 s"; break; fi
  first=0
done
exec 9>&-
python3 -I $O/reach.py main52=$O/old-2026-11-04-main52-seg3-STATE.10,$O/old-2026-11-04-main52-seg3-STATE.9,$O/old-2026-11-04-main52-seg3-STATE.8 exact63=$O/law-2026-11-05-exact63-seg5-STATE.8,$O/law-2026-11-05-exact63-seg5-STATE.7,$O/law-2026-11-05-exact63-seg5-STATE.6
echo "REACH exit $(date -u +%H:%M:%S)"
