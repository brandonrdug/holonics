#!/bin/bash
# The slip against the substitution alone (§16.43): from main52 seg3's last state (1.011 nats a place), the six held problems,
# 64 sweeps (the same first pass for both: its draws do not read the slip), then one refine pass, without the slip and with it
# (FIELD_SLIP=1), the same keyed draws. Read: the restated results after `>>` written exactly, by dropped or added digits.
# Projection from the development read (slip56/dev: the first pass 6.6 s, a slip revisit step 2.85 s, the longest answer 442
# places): the plain pass about 50 s, deadline 300 s; the slip pass 6.6 + 442 x 2.85 = 1,266 s, stopped at 1,700 s, deadline
# 1,800 s. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-04-slip56; BIN=$O/field_pass; S=$W/.local/run/2026-11-04-main52/seg3; ST=$S/STATE.10
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "SLIP LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) state $(sha $ST) lock taken $(date -u +%H:%M:%S)"
A="$ST $(sha $ST) $S/CODEC $(sha $S/CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 6 64 1"
rm -rf $O/plain $O/slip
$M plain timeout 300 $BIN train complete-language sample-field $A 280000 $O/plain > $O/plain.log 2>&1
grep -E '^FIELD_SAMPLE |MEASURE|rror|panic' $O/plain.log | cut -c1-200
FIELD_SLIP=1 $M slip timeout 1800 $BIN train complete-language sample-field $A 1700000 $O/slip > $O/slip.log 2>&1
grep -E '^FIELD_SAMPLE |MEASURE|rror|panic' $O/slip.log | cut -c1-200
echo "SLIP exit $(date -u +%H:%M:%S)"
