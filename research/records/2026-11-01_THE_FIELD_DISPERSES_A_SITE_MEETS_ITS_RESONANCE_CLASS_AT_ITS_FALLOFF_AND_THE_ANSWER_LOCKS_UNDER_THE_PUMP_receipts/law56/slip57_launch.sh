#!/bin/bash
# The slip, priced with its importance weights and read (§16.43): slip56's slip pass again from main52 seg3's last state, the
# six held problems, 64 sweeps and one refine pass with FIELD_SLIP=1, now with the stay and the insert priced on their window
# less their drawn place's own code, and every proposal read (FIELD_SAMPLE_SLIP_MOVES). The plain pass is slip56's (the same
# first pass and keyed draws). Projection: slip56's slip pass 977 s; this reads two places fewer of each proposal's 33;
# stopped at 1,700 s, deadline 1,800 s. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
O=$W/.local/run/2026-11-04-slip57; BIN=$O/field_pass; S=$W/.local/run/2026-11-04-main52/seg3; ST=$S/STATE.10
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "SLIP LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) state $(sha $ST) lock taken $(date -u +%H:%M:%S)"
A="$ST $(sha $ST) $S/CODEC $(sha $S/CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 6 64 1"
rm -rf $O/slip
FIELD_SLIP=1 $M slip timeout 1800 $BIN train complete-language sample-field $A 1700000 $O/slip > $O/slip.log 2>&1
grep -E '^FIELD_SAMPLE |^FIELD_SAMPLE_SLIP_MOVES|MEASURE|rror|panic' $O/slip.log | cut -c1-200
echo "SLIP exit $(date -u +%H:%M:%S)"
