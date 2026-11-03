#!/bin/bash
# The 45-minute GSM8K run under every law of November 3 (#611–#623): the writer, whole and answer masks drawn at τ = u² and
# weighed back, silent open places, steps at their certified size, the strand pair contact, D 32, H 4, n 8, still 2, f 32,
# K 4, section 16, rate 8, growth by copies of the width and merge (heads kept) when the withheld code stops falling.
# Question: does the joint code flatten near the fit's 2.6 bits, or does growth push it lower.
# Projection (k4's five measured laps, 109 to 113 s, 121 s with their reads): about 22 laps in 2,700 s; lap bound 160 s, a
# grown lap 200 s (the heads hold the card's time: a trained D 64, H 4 lap read 288 s against 270 s at D 32 at six ticks);
# STOP_MS 2,700,000, outer 2,760 s; then the first 6 held answers written one place a sweep (1,229 sweeps; about 11 ms a
# problem-sweep at four ticks, 81 s; STOP_MS 150,000, outer 170 s). The whole under 49 minutes. RTX 4080 SUPER under
# .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-03-run35; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 300 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
START=$(date +%s)
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
$M train timeout 2760 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 160000 200000 2700000 $O/train > $O/train.log 2>&1
grep -E '^FIELD_(LAP|HELD|JOINT |STOPPED|LAPS_HELD|GROW)|^MEASURE' $O/train.log | awk '{for(i=1;i<=NF;i++) if ($i ~ /^(lap|context|own_bits_a_byte|answer|ms|width|reason)=/ || $i ~ /^FIELD|^MEASURE/) printf "%s ", $i; print ""}'
STATE=$(ls -t $O/train/STATE.* 2>/dev/null | head -1)
[ -n "$STATE" ] || { echo "FIELD_RUN exit no state"; exit 1; }
U="$G/UNITS0 $(sha $G/UNITS0)"
$M sample timeout 170 $BIN train complete-language sample-field $STATE $(sha $STATE) $O/train/CODEC $(sha $O/train/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 150000 $O/sample > $O/sample.log 2>&1
grep -E '^FIELD_SAMPLE |^MEASURE' $O/sample.log
echo "FIELD_RUN exit at_s=$(( $(date +%s) - START ))"
