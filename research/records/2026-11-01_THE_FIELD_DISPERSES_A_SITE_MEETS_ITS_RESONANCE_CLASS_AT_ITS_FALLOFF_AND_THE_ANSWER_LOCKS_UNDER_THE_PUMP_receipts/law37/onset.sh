#!/bin/bash
# §16.35's copy onset read: the copy lab's terrains (make_copy_toy.py) for long enough to meet GSM8K's onset (about 12,800
# steps there; 125 steps a lap here, so about 100 laps): near for 300 laps, far for 100, today's declaration from a fresh
# founding each. Then the sampled card parity of the closing writer (law27's parity read: 3 sections, 8 withheld problems,
# one write of 8 sweeps). Projection: near 1.5 s a lap (sweep.txt's 1,470 ms), 300 laps 450 s; far 7.6 s a lap, 100 laps
# 760 s; lap bounds 30 s and 40 s, STOP_MS 900,000 and 1,200,000, outer 960 s and 1,260 s; the parity 330 s, deadline 400 s.
# The whole under 45 minutes once the card is free (the lock waits for run37, whose deadline ends near 21:25 UTC).
# RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy35; BIN=$W/.local/run/2026-11-03-void35/field_pass_close; PBIN=$W/.local/run/2026-11-03-refine36/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 5400 9 || { echo "SWEEP LOCK_BUSY"; exit 75; }
run() {
  local name=$1 lap=$2 stop=$3 outer=$4 laps=$5; shift 5
  local T="$G/UNITS0 $(sha $G/UNITS0) $O/$name/TRAIN.txt $(sha $O/$name/TRAIN.txt) $O/$name/HELD.txt $(sha $O/$name/HELD.txt) $K $(sha $K)"
  rm -rf $O/o_$name
  timeout $outer $BIN train complete-language train-field $T 32 4 8 2 32 4 16 $laps 8 $lap $lap $stop $O/o_$name > $O/o_$name.log 2>&1
  echo "$name: laps $(grep -c '^FIELD_LAP ' $O/o_$name.log) lap_ms $(grep -E '^FIELD_LAP ' $O/o_$name.log | tail -1 | sed -E 's/.* ms=([0-9]+).*/\1/') grow $(grep '^FIELD_GROW ' $O/o_$name.log | sed -E 's/.*lap=([0-9]+) width=([0-9]+).*/lap \1 to \2/' | tr '\n' ' ')"
  grep -E '^FIELD_JOINT lap=' $O/o_$name.log | sed -E 's/.*lap=([0-9-]+) .*own_bits_a_byte=([0-9.]+) foil_bits_a_byte=([0-9.]+) information_bits_a_byte=([0-9.-]+).*/\1 \2 \4/' | awk '$1 % 10 == 9 || $1 < 2 {print "  lap " $1 " own " $2 " information " $3}'
}
run near 30000 900000 960 300
run far 40000 1200000 1260 100
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
echo "# parity binary sha $(sha $PBIN)"
FIELD_PARITY_PACE=8 $M parity timeout 400 $PBIN parity complete-language parity-field $T 32 4 8 2 32 2 16 3 8 1 1 8 8 > $O/parity35.log 2>&1
grep -E 'unequal|equal|PARITY|MEASURE' $O/parity35.log | tail -12
