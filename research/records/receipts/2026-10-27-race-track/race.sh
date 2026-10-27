#!/bin/bash
# The race track (agent-inferred, October 27): laps of the plain gated two-ladder tower on the
# card, one lap a segment under the card lock, each lap followed by its writing on the card from
# the same prompts and keys, so laps differ only by the learner. The lock is released between
# segments so other card work can run. No lap starts after HOURS from launch.
#
#   race.sh BIN LOCK RACE OUT HOURS LAP_S WRITE_S WINDOW_MS
#
# BIN: tower_pass (release build). LOCK: the card lock (the main checkout's .local/gpu.lock).
# RACE: the composed passage's directory (compose_race_passage.py). OUT: where the laps, their
# logs and their writings go (lapK/, lapK.log, writeK/, writeK.log). LAP_S and WRITE_S: each
# segment's fixed deadline in seconds, from the opening read's projection; never raised.
# WINDOW_MS: the opening read's largest 32-section window. After each lap's writing, the race stops
# if any of that lap's windows (the stretch to its first TOWER_SECTION not counted) passed 1.12
# times WINDOW_MS, or if fewer than two of its windows were read (fail closed).
set -u
BIN=$1; LOCK=$2; RACE=$3; OUTDIR=$4; HOURS=$5; LAP=$6; WRITE=$7; WINDOW=$8
sha() { sha256sum "$1" | cut -d' ' -f1; }
T=$RACE/TRAIN.classes; D=$RACE/DEV.classes; R=$RACE/DEV.roles; K=$RACE/KEYS
P=$RACE/PROMPTS.classes; RK=$RACE/RELEASE_KEYS
TS=$(sha "$T"); DS=$(sha "$D"); RS=$(sha "$R"); KS=$(sha "$K"); PS=$(sha "$P"); RKS=$(sha "$RK")
mkdir -p "$OUTDIR" || exit 1
echo "RACE_START bin=$(sha "$BIN") train=$TS dev=$DS roles=$RS keys=$KS prompts=$PS release_keys=$RKS hours=$HOURS lap_s=$LAP write_s=$WRITE window_ms=$WINDOW at=$(date -u +%FT%TZ)"
end=$(( $(date +%s) + HOURS * 3600 ))
k=0
FROM=()
while [ "$(date +%s)" -lt "$end" ]; do
  OUT=$OUTDIR/lap$k
  echo "RACE_LAP_START lap=$k at=$(date -u +%FT%TZ)"
  flock "$LOCK" timeout "$LAP" "$BIN" train complete-language train-two-ladder-tower-classes 257 \
    "$T" "$TS" "$D" "$DS" "$R" "$RS" "$K" "$KS" 64 128 256 4 320 128 1 7 "$OUT" "${FROM[@]}" > "$OUT.log" 2>&1
  status=$?
  grep -E "^(TOWER_SECTION|TOWER_PASS|TOWER_STATE|TOWER_CARD|TOWER_REALIZATION|TOWER_DONE)" "$OUT.log" | sed "s/^/lap=$k /"
  echo "RACE_LAP_END lap=$k status=$status at=$(date -u +%FT%TZ)"
  [ "$status" -eq 0 ] || exit "$status"
  STATE=$OUT/STATE.0
  flock "$LOCK" timeout "$WRITE" "$BIN" release complete-language release-tower-classes \
    "$STATE" "$(sha "$STATE")" "$P" "$PS" "$RK" "$RKS" 1024 1 "$OUTDIR/write$k" > "$OUTDIR/write$k.log" 2>&1
  status=$?
  echo "RACE_WRITE lap=$k status=$status $(grep -E '^(CLASSES_RELEASE_DONE|TOWER_CARD)' "$OUTDIR/write$k.log" | tr '\n' ' ') at=$(date -u +%FT%TZ)"
  [ "$status" -eq 0 ] || exit "$status"
  # The window stop.
  elapsed=$(grep -E '^TOWER_SECTION ' "$OUT.log" | sed -nE 's/.* elapsed_ms=([0-9]+).*/\1/p')
  read_windows=$(printf '%s\n' "$elapsed" | grep -c '^[0-9]')
  if [ "$read_windows" -lt 2 ]; then
    echo "RACE_STOP lap=$k reason=windows_unread windows=$read_windows at=$(date -u +%FT%TZ)"
    exit 4
  fi
  widest=$(printf '%s\n' "$elapsed" | awk 'NR > 1 { d = $1 - p; if (d > m) m = d } { p = $1 } END { print m + 0 }')
  echo "RACE_WINDOW lap=$k widest_ms=$widest opening_ms=$WINDOW limit_ms=$(( WINDOW * 112 / 100 ))"
  if [ $(( widest * 100 )) -gt $(( WINDOW * 112 )) ]; then
    echo "RACE_STOP lap=$k reason=window widest_ms=$widest opening_ms=$WINDOW at=$(date -u +%FT%TZ)"
    exit 4
  fi
  FROM=("$STATE" "$(sha "$STATE")")
  k=$((k + 1))
  # The lock is free here; a card job waiting on it (a parity read, another thread's run) takes it
  # before the next lap asks again.
  sleep 5
done
echo "RACE_DONE laps=$k at=$(date -u +%FT%TZ)"
