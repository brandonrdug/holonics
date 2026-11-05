#!/bin/bash
# Refinement is the field's own one-place resampling (§16.47, the unified-theory reading of November 5, 14:47): each pass
# walks each problem's keyed order of all its answer places, passing over a place past the boundary when its turn comes; a
# place before the last letter draws from its face restricted to the letters, the last letter and the boundary place from
# their whole faces, so the end moves one place in or out a draw. Read on path75's segment 1 state with the same 32 held
# problems and keys as that segment's write (the state's own hash), so the sweeps are identical and only the three refine
# passes differ.
# Prediction, fixed before launch (that reading): the refine passes move the mean written length under 3 places (the old
# law -2.0 on this state), and the share of written words in the training vocabulary stays at least 0.73 (the old 0.760).
# Rule: if so the law stands, and more passes can go to words without cutting answers; a share under 0.73 withdraws it.
# Projection: path75's segment 1 write measured 1,282 s; the writer's stop 2,400 s, outer 2,700 s. RTX 4080 SUPER under
# .local/gpu.lock (one window between the chains' steps; the lock waited on up to 7,200 s), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; R=$W/.local/run
O=$R/2026-11-05-refine81; BIN=$O/field_pass; P=$R/2026-11-05-path75; S=$P/seg1/STATE.2; CODEC=$P/seg1/CODEC
A=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "REFINE81 LOCK_BUSY"; exit 75; }
echo "# refine81 binary $(sha $BIN) state $(sha $S | cut -c1-16) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/write
$M write timeout 2700 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 32 1229 3 2400000 $O/write > $O/write.log 2>&1
exec 9>&-
grep -E '^FIELD_LENGTH|^MEASURE|rror|panic' $O/write.log | cut -c1-200
python3 -I - $O/write $P/seg1_write <<'PY'
import csv, statistics, sys
U = 1 << 20
def load(d):
    l = {}
    for r in csv.DictReader(open(f"{d}/LENGTH.tsv"), delimiter="\t"):
        l.setdefault(int(r["problem"]), {})[(int(r["pass"]), int(r["read"]))] = int(r["length"]) / U
    e = {int(r["problem"]): (int(r["held"]), int(r["written"])) for r in csv.DictReader(open(f"{d}/ENDS.tsv"), delimiter="\t")}
    return l, e
(new, ne), (old, oe) = load(sys.argv[1]), load(sys.argv[2])
sweeps_equal = all({k: v for k, v in new[p].items() if k[0] == 0} == {k: v for k, v in old[p].items() if k[0] == 0} for p in new)
print("sweeps equal to the segment's write:", sweeps_equal)
for name, l, e in (("new", new, ne), ("old", old, oe)):
    after = {p: l[p][max(k for k in l[p] if k[0] == 0)] for p in l}
    moved = [e[p][1] - after[p] for p in l]
    short = [p for p in l if e[p][1] < e[p][0]]
    print(f"{name}: written less held {statistics.mean(e[p][1] - e[p][0] for p in l):+.1f}, the refine passes moved the length {statistics.mean(moved):+.1f} (range {min(moved):+.0f} to {max(moved):+.0f}), {sum(1 for p in l if e[p][1] > e[p][0])} longer and {len(short)} shorter, reads {max(max(k[1] for k in l[p]) for p in l)}")
PY
python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/write/SAMPLE.tsv
python3 -I $A/law56/written_restatements.py $O/write/SAMPLE.tsv
python3 -I $O/endings.py $G/HELD128.txt $O/write/SAMPLE.tsv
echo "REFINE81 exit $(date -u +%H:%M:%S)"
