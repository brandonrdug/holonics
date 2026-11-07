#!/bin/bash
# The merged tree's card suite (the worker's tangent-once and tensor-core score tangent beside the central squares and
# energies), then lap 11's development read (theory, November 7, 07:40: each problem's truth formed once for all its blocks;
# the block size from the acceptance's own slope, log2 k* += (1 + slope)/4) from lap 10's STATE.stopped (its family lengths
# carried). Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads; outer deadline 300 s for the suite, 180 s for
# the read.
set -u
export RAYON_NUM_THREADS=8 CARGO_BUILD_JOBS=8 PATH=/opt/cuda/bin:$PATH
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap11; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap10/lap/STATE.stopped
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
(cd $ROOT/.local/wt/writer107 && timeout 300 cargo test --release -p holonics-cuda --test field_energy -- --include-ignored --test-threads=1 --skip a_writer_release > $O/suite.log 2>&1; echo "suite rc $?"; grep -E "test result|FAILED|panicked" $O/suite.log)
D=$O/dev; rm -rf $D
$M dev timeout 180 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 3600000 60000 $D > $D.log 2>&1
grep -E '^FIELD_(STOPPED|KERNEL_ACCEPT|CARD )|^MEASURE|rror|panic' $D.log | cut -c1-400
grep '^FIELD_KERNEL lap' $D.log | python3 -I -c "
import sys
rows=[dict(kv.split('=') for kv in l.split()[1:]) for l in sys.stdin]
ms=sum(int(r['ms_section']) for r in rows); bl=sum(int(r['blocks']) for r in rows)
ks=[int(r['k_star']) for r in rows]
print(f'sections={len(rows)} problems={16*len(rows)} blocks={bl} ms_a_problem={ms/(16*len(rows)):.2f} lap_projection_s={24685*ms/(16*len(rows))/1000:.0f} accept_milli_mean={sum(int(r[\"accept_milli\"]) for r in rows)/len(rows):.0f} k_star first {ks[:6]} last {ks[-6:]}')
"
echo "MAIN exit $(date -u +%H:%M:%S)"
