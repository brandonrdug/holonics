#!/bin/bash
# The slip's cost, a development read (§16.43): sample-field on main52 seg3's last state, the six held problems, 64 sweeps (19
# places a problem a sweep), one refine pass whose revisits may slip (FIELD_SLIP=1), stopped at 150 s; the progress lines give
# the time a revisit step costs. Unmeasured: planned at one to three minutes; deadline 240 s. RTX 4080 SUPER under
# .local/gpu.lock (idle), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-04-slip56; BIN=$O/field_pass; S=$W/.local/run/2026-11-04-main52/seg3
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "SLIP LOCK_BUSY"; exit 75; }
ST=$(ls -t $S/STATE.* | head -1)
echo "# binary sha $(sha $BIN) state $(basename $ST) lock taken $(date -u +%H:%M:%S)"
rm -rf $O/dev
FIELD_SLIP=1 $M dev timeout 240 $BIN train complete-language sample-field $ST $(sha $ST) $S/CODEC $(sha $S/CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 6 64 1 150000 $O/dev > $O/dev.log 2>&1
grep -E '^FIELD_SAMPLE|^FIELD_CARD |MEASURE|rror|panic' $O/dev.log | cut -c1-200
echo "SLIP exit $(date -u +%H:%M:%S)"
