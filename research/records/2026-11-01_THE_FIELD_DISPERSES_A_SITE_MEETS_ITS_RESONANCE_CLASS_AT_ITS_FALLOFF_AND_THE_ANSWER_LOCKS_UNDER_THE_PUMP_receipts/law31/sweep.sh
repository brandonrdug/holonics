#!/bin/bash
# §16.31's fast lab: the triple terrain read under one declaration a variant, 20 laps each (the base measured 3.0 to 3.5 s a
# lap; a variant of four times the sections or ticks about 15 s), lap bound 30 s, STOP_MS 240,000, outer 260 s a variant; the
# held context and joint codes at laps 4, 9, 14 and 19 against the two-sided tables' 2.456 (one neighbour) and 1.436 (two).
# RTX 4080 SUPER under .local/gpu.lock.
set -u
ROOT=${ROOT:?the repository root}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy31; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 900 9 || { echo "SWEEP LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $O/TRAIN.txt $(sha $O/TRAIN.txt) $O/HELD.txt $(sha $O/HELD.txt) $K $(sha $K)"
run() {
  local name=$1; shift
  rm -rf $O/s_$name
  timeout 260 $BIN train complete-language train-field $T "$@" 30000 30000 240000 $O/s_$name > $O/s_$name.log 2>&1
  echo "$name: $(grep -E '^FIELD_HELD lap=(4|9|14|19) ' $O/s_$name.log | sed -E 's/.*lap=([0-9]+) .* context=([0-9.]+).*/L\1 ctx \2/' | tr '\n' ' ') joint19 $(grep -E '^FIELD_JOINT lap=19 ' $O/s_$name.log | sed -E 's/.*own_bits_a_byte=([0-9.]+).*/\1/') laps $(grep -c '^FIELD_LAP ' $O/s_$name.log) lap_ms $(grep -E '^FIELD_LAP ' $O/s_$name.log | tail -1 | sed -E 's/.* ms=([0-9]+).*/\1/') grow $(grep -c '^FIELD_GROW ' $O/s_$name.log)"
}
run base   32 4 8 2 32 6 16 20 8
run k2     32 4 8 2 32 2 16 20 8
run sec4   32 4 8 2 32 6 4 20 8
run rate7  32 4 8 2 32 6 16 20 7
run f128   32 4 8 2 128 6 16 20 8
run n16    32 4 16 2 32 6 16 20 8
run still0 32 4 8 0 32 6 16 20 8
