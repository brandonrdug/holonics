#!/bin/bash
# §16.44's acceptance read on the last three laps' states of a run (the all-open read swings 5.05 to 6.15 between laps
# under the old law, so one state is not a reading): restate-field with the first-state read under BINARY (old or law) on
# each STATE, then acceptance.py. Usage: trio.sh NAME BINARY STATE... Projection: 70 s a state (accept61's law read), so
# three states 210 s; deadline 240 s each. RTX 4080 SUPER under .local/gpu.lock (one window between blank60's steps), 24
# host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-accept61; CODEC=$R/2026-11-04-lane45/CODEC; NAME=$1; BIN=$2; shift 2
A=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts/law60/acceptance.py
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "TRIO LOCK_BUSY"; exit 75; }
echo "# $NAME binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
for ST in "$@"; do
  tag=$NAME-$(basename $(dirname $ST))-$(basename $ST)
  rm -rf $O/$tag
  $M $tag timeout 240 $BIN train complete-language restate-field $ST $(sha $ST) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 $O/$tag > $O/$tag.log 2>&1
  echo "$tag $(grep -E '^FIELD_RESTATE_FIRST' $O/$tag.log) $(grep -E '^MEASURE' $O/$tag.log | sed 's/.*wall_s=/wall_s=/')"
  python3 -I $A $O/$tag/RESTATEMENTS.tsv | sed 's#.*: ##'
done
echo "TRIO exit $(date -u +%H:%M:%S)"
