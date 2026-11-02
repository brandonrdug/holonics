#!/usr/bin/env bash
# Record 2026-10-31 (a question's number…) §6: one run of the plan from C′'s founding keys at 160 streams,
# the §45 declaration (64 128 256 6 160 128 40 8, rate 2^(-8), 40 laps, no FROM), the held-out partition
# COPY.roles; then the g50 receipt at laps 10, 20, 30, 40 (STATE.9, 19, 29, 39): the flux read and the FREE
# (512) and MARKS (16) releases at the four key files GKEYS, GKEYS_b, _c, _d.
#   brun.sh NAME ROUTE CODEC DEADLINE      CODEC = units (the committed founding) | u0 (no merges)
# Environment passes through to the trainer only for TOWER_PARTICIPATION_FROM / _SECTION / TOWER_LAP_SECTIONS.
set -u
NAME=$1; ROUTE=$2; CODEC=$3; LIMIT=$4; LAPS=${LAPS:-40}
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
G=$R/gsm8k
if [ $CODEC = units ]; then
  U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS; X=""
else
  U=$G/UNITS0; X=.u0
fi
BIN=${BIN:-$R/bin/tower_pass-46a}
E=$R/race/bytes-1101; mkdir -p $E
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LOCK_BUSY"; exit 75; }
PF=${TOWER_PARTICIPATION_FROM-}; PS=${TOWER_PARTICIPATION_SECTION-}; LS=${TOWER_LAP_SECTIONS-}
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE TOWER_WINDOW_SECTIONS TOWER_FACE_GLOBAL TOWER_LAP_SECTIONS TOWER_PROMPT_SEPARATOR TOWER_PARTICIPATION_FROM TOWER_PARTICIPATION_SECTION TOWER_NEXT_SECTION
ENVS=(); [ -n "$PF" ] && ENVS+=(-E TOWER_PARTICIPATION_FROM=$PF); [ -n "$PS" ] && ENVS+=(-E TOWER_PARTICIPATION_SECTION=$PS); [ -n "$LS" ] && ENVS+=(-E TOWER_LAP_SECTIONS=$LS)
echo "BIN=$(sha $BIN) UNITS=$(sha $U) ROUTE=$ROUTE LAPS=$LAPS LIMIT=$LIMIT ENV=${ENVS[*]} NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
O=$E/$NAME
if [ "${RECEIPT_ONLY:-0}" != 1 ]; then rm -rf $O
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $O.vram &
VRAM=$!
# Early stop (the waiting standard): a lap among the first three past the per-lap bound BOUND_MS stops the run.
if [ -n "${BOUND_MS:-}" ]; then
  : > $O.log
  ( tail -F -n0 --pid=$$ $O.log 2>/dev/null | awk -v b=$BOUND_MS -v o=$O '/^TOWER_PASS /{ if (match($0,/pass_ms=[0-9]+/)) { v=substr($0,RSTART+8,RLENGTH-8)+0; n++; if (v>b) { print "EARLY_STOP lap " n " pass_ms=" v " bound=" b > (o ".stop"); system("pkill -f \"^[^ ]*tower_pass[^ ]* train complete-language .* " o "$\""); exit } if (n>=3) exit } }' ) &
fi
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 "${ENVS[@]}" \
  python3 -I $R/measure.py $NAME timeout $LIMIT $BIN train complete-language $ROUTE $U $(sha $U) \
  $G/TRAIN.bytes $(sha $G/TRAIN.bytes) $G/DEV.bytes $(sha $G/DEV.bytes) $G/COPY.roles $(sha $G/COPY.roles) \
  $P/KEYS2 $(sha $P/KEYS2) 64 128 256 6 160 128 $LAPS 8 $O > $O.log 2>&1
echo "RUN_END $NAME rc=$? $(grep -E 'TOWER_CARD|MEASURE|rror' $O.log | tr '\n' ' ') $(cat $O.stop 2>/dev/null)"
kill $VRAM; echo "VRAM_PEAK_MIB $NAME=$(sort -n $O.vram | tail -1) baseline=$(head -1 $O.vram)"
fi
[ "${RECEIPT:-1}" = 1 ] || exit 0
for lap in ${RECEIPT_LAPS:-9 19 29 39}; do
  S=$O/STATE.$lap; n=$((lap+1))
  [ -f "$S" ] || { echo "RECEIPT lap $n absent"; continue; }
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 \
    python3 -I $R/measure.py flux-$n timeout 300 $BIN read complete-language read-tower-race $S $(sha $S) \
    $G/DEV.units$X $(sha $G/DEV.units$X) $G/PROMPTS6.units$X $(sha $G/PROMPTS6.units$X) 24 128 $O-flux-$n > $O-flux-$n.log 2>&1
  for keys in GKEYS GKEYS_b GKEYS_c GKEYS_d; do
    for kind in FREE:512 MARKS:16; do
      k=${kind%%:*}; m=${kind#*:}
      systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -E TOWER_END_CLASS=30 -E TOWER_PROMPT_SEPARATOR=31 \
        python3 -I $R/measure.py $k-$n-$keys timeout 300 $BIN release complete-language release-tower-classes $S $(sha $S) \
        $G/$k.prompts.units$X $(sha $G/$k.prompts.units$X) $G/$keys $(sha $G/$keys) $m 1 $O-$k-$n-$keys > $O-$k-$n-$keys.log 2>&1
    done
  done
  echo "RECEIPT lap $n done $(grep -h MEASURE $O-*-$n*.log | awk '{print $2"="$4}' | tr '\n' ' ')"
done
