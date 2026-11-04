#!/bin/bash
# The tower's first reading (the tower record's acceptance, §4): run38's lap-13 state (D 256, H 4, f 256, rate 11; joint code
# 1.820 bits a byte, the question's information 0.440) continued 45 minutes alone and 45 minutes grown in scale (packets of 6
# sites after two of its four ticks; the packets' field D 256, H 8 with 4 still, f 256, four ticks), under every law of the
# day (conservation of faces with the still heads read at any distance), growth held in both arms so they stand at one width.
# Acceptance: the tower's joint code at least 0.05 bits a byte below the field alone's after the same wall time, its question's
# information at least as high, and its written answers (three refinement passes) shown whole.
# Projection: run38's D 256 laps 192 to 208 s, 225 s with their reads; the tower's packets a sixth of the sites at twice the heads
# (a twelfth of the fine contact's pairs and heads), its lap at most 1.25 times, 280 s; about 12 and 9 laps in 2,700 s each; lap
# bounds 260 s and 320 s; STOP_MS 2,700,000, outer 2,760 s each; the writes 330 s each (refine36's 248 s at D 128, read at
# D 256: STOP_MS 450,000, outer 470 s). The whole under 110 minutes, gated on the tower's parity (tower40) reading equal.
# RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=$ROOT; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-04-run41; BIN=$O/field_pass
FROM=$W/.local/run/2026-11-03-run38/train/STATE.13
P=$W/.local/run/2026-11-03-tower40/launch2.out
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
timeout 9000 bash -c "until [ \$(grep -c 'FIELD_PARITY_DONE\|MEASURE lap=tower' $P 2>/dev/null) -ge 1 ] || grep -qE 'LOCK_BUSY|rror|panic' $P 2>/dev/null; do sleep 30; done"
if ! [ "$(grep 'FIELD_PARITY_DONE' $P | tail -1 | grep -c 'reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 releases=1 releases_unequal=0')" = 1 ]; then
  echo "TOWER_RUN parity did not read equal; no run"; exit 1
fi
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
arm() { # NAME LAPBOUND ENV
  local name=$1 bound=$2; shift 2
  rm -rf $O/$name
  env FIELD_GROWTH_HELD=1 "$@" $M $name timeout 2760 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $bound $bound 2700000 $O/$name $FROM $(sha $FROM) > $O/$name.log 2>&1
  grep -E '^FIELD_(SCALE|JOINT |LAPS_HELD|STOPPED)|^MEASURE|rror' $O/$name.log | sed -E 's/ (foil_bits_a_byte|answers|sites)=[^ ]*//g' | cut -c1-200
  local S=$(ls -t $O/$name/STATE.* 2>/dev/null | head -1)
  [ -n "$S" ] || { echo "$name no state"; return; }
  $M ${name}_write timeout 470 $BIN train complete-language sample-field $S $(sha $S) $O/$name/CODEC $(sha $O/$name/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 3 450000 $O/${name}_write > $O/${name}_write.log 2>&1
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/${name}_write.log
  python3 -I $W/.local/run/2026-11-03-refine36/words.py $G/TRAIN.txt $O/${name}_write/SAMPLE.tsv
}
arm alone 260000 FIELD_NONE=1
arm tower 320000 FIELD_SCALE_FIRST=6
echo "FIELD_RUN exit"
