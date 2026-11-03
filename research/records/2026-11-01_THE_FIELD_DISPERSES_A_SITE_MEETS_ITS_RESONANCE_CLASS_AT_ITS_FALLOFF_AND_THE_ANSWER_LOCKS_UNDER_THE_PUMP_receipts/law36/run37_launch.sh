#!/bin/bash
# Continues run36's lap-19 state (D 64, H 4, f 64, rate 9; joint code 2.164 bits a byte; the question's information rose from
# 0.018 to 0.247 bits a byte between run36's laps 7 and 18, the context read 0.526) under the same training laws, the binary
# carrying the closing writer (a drawn void ends the answer, §16.35) and its place read. Question: does the question's
# information keep rising past 0.25 and the joint keep falling at about 0.02 a lap, and do the written answers carry their
# question's words? A second growth (to D 128, heads kept) stays allowed when the withheld code stops falling.
# Projection (run36's D 64 laps, 115 to 125 s, 140 s with their reads; a D 128 lap 185 s): about 19 laps in 2,700 s; lap bound
# 160 s, a grown lap 220 s; STOP_MS 2,700,000, outer 2,760 s; then six held answers by the closing writer (run36's state 64 s;
# STOP_MS 150,000, outer 170 s). The whole under 49 minutes once the card is free (the lock waits for the copy lab, under
# 15 minutes). RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-03-run37; BIN=$O/field_pass
FROM=$W/.local/run/2026-11-03-run36/train/STATE.19
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 1500 9 || { echo "FIELD_RUN LOCK_BUSY"; exit 75; }
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
