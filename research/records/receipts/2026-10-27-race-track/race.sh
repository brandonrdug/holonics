#!/bin/bash
# The race track (agent-inferred, October 27): laps of the plain gated two-ladder tower on the
# card, one lap a segment under the card lock, each lap followed by its writing on the card from
# the same prompts and keys, so laps differ only by the learner. The lock is released between
# segments so other card work can run. No lap starts after HOURS from launch.
#
#   race.sh BIN LOCK RACE HOURS LAP_S WRITE_S
#
# BIN: tower_pass (release build). LOCK: the card lock (the main checkout's .local/gpu.lock).
# RACE: the composed passage's directory (compose_race_passage.py). LAP_S and WRITE_S: each
# segment's fixed deadline in seconds, from the opening read's projection; never raised.
set -u
BIN=$1; LOCK=$2; RACE=$3; HOURS=$4; LAP=$5; WRITE=$6
sha() { sha256sum "$1" | cut -d' ' -f1; }
T=$RACE/TRAIN.classes; D=$RACE/DEV.classes; R=$RACE/DEV.roles; K=$RACE/KEYS
P=$RACE/PROMPTS.classes; RK=$RACE/RELEASE_KEYS
TS=$(sha "$T"); DS=$(sha "$D"); RS=$(sha "$R"); KS=$(sha "$K"); PS=$(sha "$P"); RKS=$(sha "$RK")
echo "RACE_START bin=$(sha "$BIN") train=$TS dev=$DS roles=$RS keys=$KS prompts=$PS release_keys=$RKS hours=$HOURS lap_s=$LAP write_s=$WRITE at=$(date -u +%FT%TZ)"
end=$(( $(date +%s) + HOURS * 3600 ))
k=0
FROM=()
while [ "$(date +%s)" -lt "$end" ]; do
  OUT=$RACE/lap$k
  echo "RACE_LAP_START lap=$k at=$(date -u +%FT%TZ)"
  flock "$LOCK" timeout "$LAP" "$BIN" train complete-language train-two-ladder-tower-classes 257 \
    "$T" "$TS" "$D" "$DS" "$R" "$RS" "$K" "$KS" 64 128 256 4 320 128 1 7 "$OUT" "${FROM[@]}" > "$OUT.log" 2>&1
  status=$?
  grep -E "^(TOWER_SECTION|TOWER_PASS|TOWER_STATE|TOWER_CARD|TOWER_REALIZATION|TOWER_DONE)" "$OUT.log" | sed "s/^/lap=$k /"
  echo "RACE_LAP_END lap=$k status=$status at=$(date -u +%FT%TZ)"
  [ "$status" -eq 0 ] || exit "$status"
  STATE=$OUT/STATE.0
  flock "$LOCK" timeout "$WRITE" "$BIN" release complete-language release-tower-classes \
    "$STATE" "$(sha "$STATE")" "$P" "$PS" "$RK" "$RKS" 1024 1 "$RACE/write$k" > "$RACE/write$k.log" 2>&1
  status=$?
  echo "RACE_WRITE lap=$k status=$status $(grep -E '^(CLASSES_RELEASE_DONE|TOWER_CARD)' "$RACE/write$k.log" | tr '\n' ' ') at=$(date -u +%FT%TZ)"
  [ "$status" -eq 0 ] || exit "$status"
  FROM=("$STATE" "$(sha "$STATE")")
  k=$((k + 1))
  # The lock is free here; a card job waiting on it (a parity read, another thread's run) takes it
  # before the next lap asks again.
  sleep 5
done
echo "RACE_DONE laps=$k at=$(date -u +%FT%TZ)"
