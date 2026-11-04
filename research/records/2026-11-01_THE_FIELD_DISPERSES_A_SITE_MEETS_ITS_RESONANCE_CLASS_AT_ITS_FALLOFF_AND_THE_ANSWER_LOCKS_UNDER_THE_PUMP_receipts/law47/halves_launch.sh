#!/bin/bash
# The half-tick reading (§16.40's next loop): the volume and the expansion at each tick's opening and after its current (the
# pair contact's chart), so each tick splits into the current's half and the pair contact's half, across the training's states
# (each v12 state's head line rewritten to v13 with one lane, its body byte-equal) and tonight's two arms. On the first 8 held
# problems read with their neighbours. Projection: one to four seconds a state (expand42's reads: 0.8 s at D 256, 3.3 s at
# D 512), under two minutes in all; each read's outer timeout 300 s. RTX 4080 SUPER under .local/gpu.lock.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
R=$W/.local/run; O=$R/2026-11-04-halves47; BIN=$O/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "HALVES LOCK_BUSY"; exit 75; }
U="$G/UNITS0 $(sha $G/UNITS0)"
read_state() { # NAME STATE CODEC
  [ -f "$2" ] || { echo "$1 absent"; return; }
  local S=$O/$1.state
  sed '2s/^hnn-field-v12 \(.*\)$/hnn-field-v13 \1 1/' "$2" > $S
  echo "== $1"
  timeout 300 $BIN train complete-language expansion-field $S $(sha $S) "$3" $(sha "$3") $U $G/HELD128.txt $(sha $G/HELD128.txt) 8 2>&1 | grep -E '^FIELD_EXPANSION|rror|panic' | sed -E 's/ regions=8//; s/ delta=[0-9]+//'
  rm -f $S
}
read_state run35_lap0 $R/2026-11-03-run35/train/STATE.0 $R/2026-11-03-run35/train/CODEC
read_state run35_lap20 $R/2026-11-03-run35/train/STATE.20 $R/2026-11-03-run35/train/CODEC
read_state run36_lap9 $R/2026-11-03-run36/train/STATE.9 $R/2026-11-03-run36/train/CODEC
read_state run36_lap19 $R/2026-11-03-run36/train/STATE.19 $R/2026-11-03-run36/train/CODEC
read_state run37_lap17 $R/2026-11-03-run37/train/STATE.17 $R/2026-11-03-run37/train/CODEC
read_state run38_lap13 $R/2026-11-03-run38/train/STATE.13 $R/2026-11-03-run38/train/CODEC
read_state run41_alone $R/2026-11-04-run41/alone/STATE.11 $R/2026-11-04-run41/alone/CODEC
read_state run46_alone $R/2026-11-04-run46/alone/STATE.11 $R/2026-11-04-run46/alone/CODEC
read_state run46_laned $R/2026-11-04-run46/laned/STATE.7 $R/2026-11-04-run46/laned/CODEC
echo "HALVES exit $(date -u +%H:%M:%S)"
