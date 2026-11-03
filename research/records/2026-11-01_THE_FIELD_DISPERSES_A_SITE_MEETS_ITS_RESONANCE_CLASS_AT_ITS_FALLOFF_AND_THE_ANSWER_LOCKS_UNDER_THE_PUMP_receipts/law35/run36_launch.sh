#!/bin/bash
# Continues run35's lap-20 state (D 64 grown at lap 11, H 4, f 64, rate 9; joint code 2.598 bits a byte, still falling about
# 0.024 a lap) under the same laws and binary, growth allowed once more (to D 128, heads kept) when the withheld code stops
# falling. Question: does the fall go on at its lap-12-to-20 rate, and does a second growth buy another drop as lap 11's did
# (2.890 to 2.794 in one lap, then a steady fall where laps 8 to 11 had flattened)?
# Projection (run35's D 64 laps, 117 to 129 s, 138 s with their reads; a D 128 lap 1.33 times that, 185 s, from 16.30's trained
# D 128 against D 32 section read): about 19 laps in 2,700 s; lap bound 160 s, a grown lap 220 s; STOP_MS 2,700,000, outer
# 2,760 s; then the first 6 held answers written one place a sweep (1,229 sweeps; run35's D 64 write 74 s, 96 s at D 128;
# STOP_MS 150,000, outer 170 s). The whole under 49 minutes. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-03-run36; BIN=$O/field_pass
FROM=$W/.local/run/2026-11-03-run35/train/STATE.20
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 300 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
START=$(date +%s)
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
$M train timeout 2760 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 160000 220000 2700000 $O/train $FROM $(sha $FROM) > $O/train.log 2>&1
grep -E '^FIELD_(LAP|HELD|JOINT |STOPPED|LAPS_HELD|GROW)|^MEASURE|rror' $O/train.log | awk '{for(i=1;i<=NF;i++) if ($i ~ /^(lap|context|own_bits_a_byte|answer|ms|width|reason)=/ || $i ~ /^FIELD|^MEASURE|rror/) printf "%s ", $i; print ""}'
STATE=$(ls -t $O/train/STATE.* 2>/dev/null | head -1)
[ -n "$STATE" ] || { echo "FIELD_RUN exit no state"; exit 1; }
U="$G/UNITS0 $(sha $G/UNITS0)"
$M sample timeout 170 $BIN train complete-language sample-field $STATE $(sha $STATE) $O/train/CODEC $(sha $O/train/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 150000 $O/sample > $O/sample.log 2>&1
grep -E '^FIELD_SAMPLE |^MEASURE' $O/sample.log
echo "FIELD_RUN exit at_s=$(( $(date +%s) - START ))"
