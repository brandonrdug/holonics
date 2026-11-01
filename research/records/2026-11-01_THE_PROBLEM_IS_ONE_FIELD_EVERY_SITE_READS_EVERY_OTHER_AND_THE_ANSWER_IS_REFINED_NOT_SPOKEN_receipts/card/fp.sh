#!/usr/bin/env bash
# The field's card parity / timing under the card's lock.  fp.sh NAME DEADLINE MODE COMMAND ARGS-AFTER-KEYS…
#   MODE parity|time; COMMAND parity-field|time-field; the inputs: the bytes (UNITS0), the route's GSM8K
#   TRAIN.txt and HELD128.txt, KEYS8 (8 MiB).
set -u
NAME=$1; LIMIT=$2; MODE=$3; CMD=$4; shift 4
W=$ROOT/.local/wt/field-card
G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$W/.local/run/KEYS8
BIN=$W/target/release/examples/field_pass
O=$W/.local/run/$NAME
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
nvidia-smi --query-gpu=memory.used,utilization.gpu,utilization.memory --format=csv,noheader,nounits -lms 200 > $O.smi &
SMI=$!
echo "BIN=$(sha $BIN) at=$(date -u +%FT%TZ) $(nvidia-smi --query-gpu=memory.used --format=csv,noheader)"
systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 \
  python3 -I $ROOT/.local/wt/section-edge/.local/run/measure.py $NAME timeout $LIMIT $BIN $MODE complete-language $CMD \
  $G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K) "$@" > $O.log 2>&1
rc=$?; kill $SMI
echo "END $NAME rc=$rc board_peak_mib=$(cut -d, -f1 $O.smi | sort -n | tail -1) baseline=$(head -1 $O.smi | cut -d, -f1) $(grep -E 'FIELD_PARITY_DONE|FIELD_TIME_LAP|FIELD_TIME_RELEASES|FIELD_CARD |MEASURE|rror|refused' $O.log | tr '\n' ' ' | cut -c1-1500)"
