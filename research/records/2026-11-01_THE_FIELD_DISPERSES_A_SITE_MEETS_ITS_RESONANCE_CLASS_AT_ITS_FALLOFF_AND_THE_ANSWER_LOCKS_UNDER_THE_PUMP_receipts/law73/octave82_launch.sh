#!/bin/bash
# The answer is released by octaves of its distance from the question (§16.47, the unified-theory reading of November 5,
# 15:04): octave j holds the places at distance [2^j, 2^(j+1)) past the question, and its places open to the keyed draws
# only once every place of the earlier octaves is resolved, so the end is drawn reading at least half its answer as written.
# Read on path75's segment 1 state, untrained for it: the 128 held problems, the sweeps only (no refine pass), keyed as
# drift80 (7949c565cdd6d613), beside drift80's L(64) on the same 128 as the present order's length; the first 32's endings
# and steps beside that segment's write.
# Prediction, fixed before launch (that reading): the written length's correlation with held at least +0.45 (the written 32
# gave +0.18); the mean written within a quarter of held; the 32's written/held steps from 0.67 to at least 0.80; at least
# 28 of the 32 ending with the final line at the boundary. Rule: if so the law stands and the path law follows it next
# segment; the mean outside a quarter, the end's faces have not met these states, and the path law follows the order for one
# segment before the law is judged; the mean within but the correlation under +0.30, the content does not judge its own
# completion, and the content's faces are the subject.
# Projection: drift80 read the 128 at 2.3 s a read (150 s for 65 reads, its opening included); the octave writer reads until
# its longest answer's last place, at most the extent's 1,229 reads, 2,830 s; the writer's stop 3,000 s, outer 3,300 s.
# RTX 4080 SUPER under .local/gpu.lock (one window between the chains' steps; the lock waited on up to 7,200 s), 24 host
# threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-octave82; BIN=$O/field_pass; P=$R/2026-11-05-path75; S=$P/seg1/STATE.2; CODEC=$R/2026-11-04-lane45/CODEC
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
KEY=7949c565cdd6d613
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "OCTAVE82 LOCK_BUSY"; exit 75; }
echo "# octave82 binary $(sha $BIN) state $(sha $S | cut -c1-16) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/write
$M write timeout 3300 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 128 1229 0 3000000 $O/write 0 $KEY > $O/write.log 2>&1
exec 9>&-
grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/write.log | cut -c1-200
python3 -I - $O/write $R/2026-11-05-drift80/path75 <<'PY'
import csv, statistics, sys
U = 1 << 20
ends = {int(r["problem"]): (int(r["held"]), int(r["written"]), r["first_void_read"]) for r in csv.DictReader(open(f"{sys.argv[1]}/ENDS.tsv"), delimiter="\t")}
l64 = {}
for r in csv.DictReader(open(f"{sys.argv[2]}/LENGTH.tsv"), delimiter="\t"):
    if r["read"] == "64":
        l64[int(r["problem"])] = int(r["length"]) / U
reads = max(int(r["read"]) for r in csv.DictReader(open(f"{sys.argv[1]}/LENGTH.tsv"), delimiter="\t"))
ks = sorted(ends)
held = [ends[k][0] for k in ks]; written = [ends[k][1] for k in ks]; old = [l64[k] for k in ks]
print(f"octave writer, 128 held: written less held mean {statistics.mean(w - h for w, h in zip(written, held)):+.1f} (median {statistics.median(w - h for w, h in zip(written, held)):+.1f}), written/held {sum(written) / sum(held):.3f}, correlation with held {statistics.correlation(written, held):+.3f}; {sum(w > h for w, h in zip(written, held))} longer, {sum(w < h for w, h in zip(written, held))} shorter; reads {reads}")
print(f"present order, drift80's L(64) on the same 128: less held mean {statistics.mean(o - h for o, h in zip(old, held)):+.1f}, correlation with held {statistics.correlation(old, held):+.3f}")
w32, h32 = written[:32], held[:32]
print(f"the first 32: written/held {sum(w32) / sum(h32):.3f}, correlation {statistics.correlation(w32, h32):+.3f}")
PY
echo "== the first 32"
python3 -I $O/endings.py $G/HELD128.txt $O/write/SAMPLE.tsv 32
echo "== all 128"
python3 -I $O/endings.py $G/HELD128.txt $O/write/SAMPLE.tsv
python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/write/SAMPLE.tsv
echo "OCTAVE82 exit $(date -u +%H:%M:%S)"
