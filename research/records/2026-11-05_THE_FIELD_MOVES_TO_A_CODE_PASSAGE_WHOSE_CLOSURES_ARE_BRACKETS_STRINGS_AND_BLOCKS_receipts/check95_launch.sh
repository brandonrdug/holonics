#!/bin/bash
# The contact's carrier against its need (the unified-theory reading of November 5, 19:31: a carrier's width is its need): a
# 30 s training read of the code passage from code84's lap-0 state with FIELD_SPREAD, each tick's widest row spread, the bits
# it needs and the limbs the launch takes (at least five). Projection: 30 s plus the start, deadline 120 s. RTX 4080 SUPER under
# .local/gpu.lock.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; R=$W/.local/run; P=$ROOT/.local/data/python-codes-25k/passage
O=$R/2026-11-05-check95; BIN=$O/field_pass; K=$ROOT/.local/wt/field-card/.local/run/KEYS8; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
S=$R/2026-11-05-code84/seg1/STATE.0
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "CHECK95 LOCK_BUSY"; exit 75; }
echo "# check95 binary $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/train
FIELD_SPREAD=1 FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 timeout 120 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 30000 $O/train $S $(sha $S) > $O/train.log 2> $O/spread.log
exec 9>&-
python3 -I - $O/spread.log <<'PY'
import re, sys, collections
need, limbs = [], collections.Counter()
for line in open(sys.argv[1]):
    m = re.search(r"spread=(\d+) need_bits=(-?\d+) bound_limbs=(\d+)", line)
    if m:
        need.append(int(m[2])); limbs[int(m[3])] += 1
need.sort()
print(f"launches {len(need)}: need bits min {need[0]}, median {need[len(need)//2]}, max {need[-1]}; limbs taken {dict(limbs)}; 64-bit words the need fills: median {-(-need[len(need)//2] // 64)}")
PY
echo "CHECK95 exit $(date -u +%H:%M:%S)"
