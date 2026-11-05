#!/bin/bash
# The standing law's writer on 32 held problems (§16.45: the free clock stands; exact63 segment 5's last state), the
# writer's opening as every write: each answer place drawn from its own face over 1,229 sweeps, then three refining passes,
# keyed by the state's hash (its first six problems are segment 5's write). Read for Brandon (the output whole) and for the
# writer's length (each written answer's length against its held answer's, the unified-theory reading of November 5, 07:11).
# Projection: segment 5's write 335 s for six problems, 56 s a problem, so 1,790 s; the writer's own stop at 2,400 s, outer
# 2,700 s. RTX 4080 SUPER under .local/gpu.lock (idle), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-write71; BIN=$R/2026-11-05-exact63/field_pass; S=$R/2026-11-05-exact63/seg5/STATE.8; CODEC=$R/2026-11-05-exact63/seg5/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
A=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "WRITE LOCK_BUSY"; exit 75; }
echo "# write71 binary $(sha $BIN) state $(sha $S) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/write
$M write timeout 2700 $BIN train complete-language sample-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 3 2400000 $O/write > $O/write.log 2>&1
exec 9>&-
grep -E '^FIELD_SAMPLE |^MEASURE|rror|panic' $O/write.log | cut -c1-250
python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/write/SAMPLE.tsv
python3 -I $A/law56/written_restatements.py $O/write/SAMPLE.tsv
echo "WRITE exit $(date -u +%H:%M:%S)"
