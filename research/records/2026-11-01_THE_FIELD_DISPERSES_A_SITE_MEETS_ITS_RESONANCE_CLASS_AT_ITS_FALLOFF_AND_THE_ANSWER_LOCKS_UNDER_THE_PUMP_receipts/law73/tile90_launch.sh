#!/bin/bash
# The tiled affine map against prof87 (the same reads on the same state): first the sampled parity on the code passage (one
# section, the withheld section and a write; it stops unless every read is equal), then a profiled training read and a profiled write on path75's segment 2
# state (GSM8K), FIELD_PROFILE (every launch timed alone, the card synchronized around it, so the split is by kernel and the
# total is inflated) and FIELD_PHASES (the host's marks). The training read: 90 s of sections from that state (the cost
# read's form). The write: 32 held problems, the first 32 reads (READS 32), no refine. Projection: 90 s plus the profile's
# synchronizations (deadline 300 s); the write at 0.42 s a read unprofiled, 32 reads, deadline 300 s. RTX 4080 SUPER under
# .local/gpu.lock (waited on up to 7,200 s), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-tile90; BIN=$O/field_pass; K=$ROOT/.local/wt/field-card/.local/run/KEYS8; S=$R/2026-11-05-path75/seg2/STATE.2; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "TILE90 LOCK_BUSY"; exit 75; }
echo "# tile90 binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
P=$ROOT/.local/data/python-codes-25k/passage
TP="$G/UNITS0 $(sha $G/UNITS0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
FIELD_PARITY_PACE=8 $M parity timeout 900 $BIN parity complete-language parity-field $TP 32 4 8 2 32 2 16 1 8 1 1 8 8 > $O/parity.log 2>&1
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY_WRITES|FIELD_PARITY section|MEASURE|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
for f in faces_unequal=0 covector_unequal=0 learner_equal=true near_equal=true clocks_equal=true rows_equal=true shares_equal=true currents_equal=true; do
  grep -E 'FIELD_PARITY section' $O/parity.log | grep -qv "$f" && { echo "PARITY FAILED on $f: the chain stops"; exit 1; }
done
rm -rf $O/train $O/write
FIELD_PROFILE=1 FIELD_PHASES=1 FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M train timeout 300 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 90000 $O/train $S $(sha $S) > $O/train.log 2>&1
FIELD_PROFILE=1 FIELD_PHASES=1 $M write timeout 300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 0 280000 $O/write 32 7949c565cdd6d613 > $O/write.log 2>&1
exec 9>&-
for f in train write; do echo "== $f"; grep -E '^FIELD_CARD |^FIELD_PROFILE_SPLIT|^MEASURE' $O/$f.log | cut -c1-300; grep -E '^FIELD_PROFILE entry' $O/$f.log | sort -t= -k4 -n -r | head -12 | cut -c1-200; grep -E '^FIELD_PHASE ' $O/$f.log | cut -c1-200; done
echo "TILE90 exit $(date -u +%H:%M:%S)"
