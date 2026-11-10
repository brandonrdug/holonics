#!/bin/bash
# lap4 development read (theory, November 7, 04:05: "project one release per state on the card"; Brandon, 04:42: the release
# relaxes jointly): contrast-field on the card from energy131's tempered founding (T0), the line's training passage (24,685
# problems, sections of 16), each section released jointly (every answer place's mixture relaxed at once, its step certified on the free energy, at most 64 reads, each
# answer's length given), the exact read at 64 held places before the lap. The read stops at 180 s (STOP_MS) after a section:
# it measures the exact read, the release and the deposit per section, a projection's inputs. Card: RTX 4080 SUPER under
# .local/gpu.lock; host part 8 threads; outer deadline 300 s.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap4; BIN=$O/field_pass; A=$R/2026-11-07-energy131
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$A/TEMPERED.STATE
exec 9>$ROOT/.local/gpu.lock; flock -w 600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/dev; rm -rf $D
$M dev timeout 300 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 64 3600000 180000 $D > $D.log 2>&1
grep -E '^FIELD_|^MEASURE|rror|panic' $D.log | cut -c1-300
[ -f $D/EXACT.tsv ] && python3 -I $O/exact.py $D/EXACT.tsv
echo "MAIN exit $(date -u +%H:%M:%S)"
