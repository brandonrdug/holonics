#!/bin/bash
# The curl at lap 4 (code91 seg2, its one-rate clock) and at drafts116's lap 25 (the bare clock), beside lap 24's: whether
# training moves the faces' reciprocity. About 12 s each. RTX 4080 SUPER under .local/gpu.lock.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; O=$R/2026-11-06-truth120; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
exec 9>$ROOT/.local/gpu.lock; flock -w 600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
for pair in "lap4 $R/2026-11-06-code91/seg2/STATE.1 one" "drafts25 $R/2026-11-06-drafts116/seg/STATE.0 bare"; do
  set -- $pair
  rm -rf $O/curl_$1
  if [ $3 = bare ]; then export FIELD_CLOCK_BARE=1; else unset FIELD_CLOCK_BARE; fi
  $M curl_$1 timeout 300 $BIN train complete-language curl-field $2 $(sha $2) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 16 $O/curl_$1 > $O/curl_$1.log 2>&1
  echo "== curl $1 ($3 clock)"; grep -E '^FIELD_CURL|rror|panic' $O/curl_$1.log | cut -c1-200
  python3 -I $O/curl.py $O/curl_$1
done
echo "MAIN exit $(date -u +%H:%M:%S)"
