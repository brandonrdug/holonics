#!/bin/bash
# The writer again with its closing energy read corrected (G/T a place in nats, the write's beside the truth's): the same
# state, keys and law, so the same texts. Projection 260 s (the first run); deadline 2,831 s as before.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-write; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-pin4/lap/STATE.0
exec 9>$ROOT/.local/gpu.lock; flock 9
D=$O/write; rm -rf $D
timeout 3400 $BIN train complete-language kernel-write $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 8 128 2831412 $D > $D.log 2>&1
echo "write rc $?"; grep -E '^FIELD_WRITE_(ENERGY|EQUILIBRIUM|DONE)|rror|panic' $D.log | cut -c1-300
cmp -s $D/WRITES.txt $O/write_first/WRITES.txt && echo "texts identical to the first run" || echo "texts DIFFER from the first run"
