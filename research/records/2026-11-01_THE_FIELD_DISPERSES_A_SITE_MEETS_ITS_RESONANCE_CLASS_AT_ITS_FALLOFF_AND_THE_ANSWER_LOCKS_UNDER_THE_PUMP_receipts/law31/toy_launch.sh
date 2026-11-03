#!/bin/bash
# §16.31's conjunction probe: the field (D 32, H 4, n 8, still 2, f 32, K 6, section 16, rate 8, every law of November 3)
# trained on the triple terrain (each third byte the table T of the two before it; references: the two-sided byte table
# codes the held answers at 2.456 bits a byte from one neighbour a side, 1.436 from two, 1.277 from three). Unmeasured:
# planned as a read of up to 10 minutes, laps bound at 120 s, STOP_MS 600,000, outer 630 s. RTX 4080 SUPER, .local/gpu.lock.
set -u
ROOT=${ROOT:?the repository root}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy31; BIN=$W/target/release/examples/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 900 9 || { echo "TOY LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $O/TRAIN.txt $(sha $O/TRAIN.txt) $O/HELD.txt $(sha $O/HELD.txt) $K $(sha $K)"
rm -rf $O/train
$M train timeout 630 $BIN train complete-language train-field $T 32 4 8 2 32 6 16 40 8 120000 120000 600000 $O/train > $O/train.log 2>&1
grep -E '^FIELD_(DECLARATION|LAP|HELD|JOINT |STOPPED|LAPS_HELD|GROW)|^MEASURE|rror' $O/train.log | awk '{for(i=1;i<=NF;i++) if ($i ~ /^(lap|context|own_bits_a_byte|answer|ms|width|sections|train|reason)=/ || $i ~ /^FIELD/) printf "%s ", $i; print ""}'
