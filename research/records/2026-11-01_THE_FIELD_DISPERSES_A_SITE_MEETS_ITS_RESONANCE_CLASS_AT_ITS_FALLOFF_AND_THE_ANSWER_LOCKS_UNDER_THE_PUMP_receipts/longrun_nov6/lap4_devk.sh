#!/bin/bash
# lap4 kernel development read (theory, November 7, 05:20: "GO inside the hour after a minute's development read: acceptance
# mean and spread ... and the projection with its deadline"): contrast-field on the card from energy131's tempered founding
# (T0), the line's training passage (1,543 sections of 16), each state one Metropolis-Hastings block step from the truth
# (answer places 11 apart, keyed offset), weighed by min(1, A); the exact read at 64 held places first. Stops after the
# section past 60 s. Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads; outer deadline 180 s.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap4; BIN=$O/field_pass; A=$R/2026-11-07-energy131
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$A/TEMPERED.STATE
exec 9>$ROOT/.local/gpu.lock; flock -w 600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/devk; rm -rf $D
$M devk timeout 180 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 3600000 60000 $D > $D.log 2>&1
grep -E '^FIELD_(KERNEL|STOPPED|CARD|EXACT_READ|CONTRAST_DECL)|^MEASURE|rror|panic' $D.log | cut -c1-300
echo "MAIN exit $(date -u +%H:%M:%S)"
