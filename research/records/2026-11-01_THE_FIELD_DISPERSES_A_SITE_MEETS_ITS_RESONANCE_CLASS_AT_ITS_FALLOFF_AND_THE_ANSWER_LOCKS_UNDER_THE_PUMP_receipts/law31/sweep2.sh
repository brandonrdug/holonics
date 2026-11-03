#!/bin/bash
# §16.31's founding read on the triple terrain: the base declaration (D 32, H 4, K 6, section 16, rate 8) founded with its
# returns drawn (FIELD_FOUND_RETURNS=returns) and with the readout's lift drawn as well (=lift), 20 laps each (3.0 to 3.5 s
# a lap measured), lap bound 30 s, STOP_MS 240,000, outer 260 s a variant, against the base's context 1.945 at lap 19.
set -u
ROOT=${ROOT:?the repository root}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy31; BIN=$W/target/release/examples/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 900 9 || { echo "SWEEP LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $O/TRAIN.txt $(sha $O/TRAIN.txt) $O/HELD.txt $(sha $O/HELD.txt) $K $(sha $K)"
for which in returns lift; do
  rm -rf $O/f_$which
  FIELD_FOUND_RETURNS=$which timeout 260 $BIN train complete-language train-field $T 32 4 8 2 32 6 16 20 8 30000 30000 240000 $O/f_$which > $O/f_$which.log 2>&1
  echo "$which: $(grep -E '^FIELD_HELD lap=(0|4|9|14|19) ' $O/f_$which.log | sed -E 's/.*lap=([0-9]+) .* context=([0-9.]+).*/L\1 ctx \2/' | tr '\n' ' ') joint19 $(grep -E '^FIELD_JOINT lap=19 ' $O/f_$which.log | sed -E 's/.*own_bits_a_byte=([0-9.]+).*/\1/') laps $(grep -c '^FIELD_LAP ' $O/f_$which.log) $(grep -E 'FIELD_FOUND_RETURNS|rror' $O/f_$which.log | head -2 | tr '\n' ' ')"
done
echo "base: $(grep -E '^FIELD_HELD lap=(0|4|9|14|19) ' $O/s_base.log | sed -E 's/.*lap=([0-9]+) .* context=([0-9.]+).*/L\1 ctx \2/' | tr '\n' ' ')"
