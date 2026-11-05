#!/bin/bash
# The answer's expected length along the writer's path (§16.47, the unified-theory reading of November 5, 09:45, its
# prediction and rule fixed before the read): length-field on boundary73 segment 1's last state, the writer of its
# 32-problem write draw for draw (its written lengths must equal that write's), each read's L = letters resolved +
# sum (1 - void mass) over the open places. Projection: segment 1's write 1,584 s; the writer's stop 2,400 s, outer 2,700 s.
# RTX 4080 SUPER under .local/gpu.lock (one window between boundary73's steps), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-length74; BIN=$O/field_pass; B=$R/2026-11-05-boundary73; S=$(ls -t $B/seg1/STATE.* | grep -v stopped | head -1); CODEC=$B/seg1/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "LENGTH LOCK_BUSY"; exit 75; }
echo "# length74 binary $(sha $BIN) state $(basename $S) $(sha $S) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/length
$M length timeout 2700 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 3 2400000 $O/length > $O/length.log 2>&1
exec 9>&-
grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/length.log | cut -c1-200
python3 -I - $O/length/ENDS.tsv $B/seg1_write/COUPLING.tsv <<'PY'
import csv, sys
a = {r["problem"]: int(r["written"]) for r in csv.DictReader(open(sys.argv[1]), delimiter="\t")}
b = {r["problem"]: int(r["written"]) for r in csv.DictReader(open(sys.argv[2]), delimiter="\t")}
print("written lengths equal to segment 1's write:", a == b)
PY
python3 -I $O/length.py $O/length
echo "LENGTH exit $(date -u +%H:%M:%S)"
