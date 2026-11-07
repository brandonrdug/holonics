#!/bin/bash
# lap 10 development read (theory, November 7, 07:24: blocks of about k* places, each its own kernel step from the truth,
# k* re-read each section from sigma^2 = -2 ln2 mean log2 A / k; each family's length carried in the state text): one
# minute from lap 9's STATE.0 (its lengths reopen at 12: lap 9's text carried none). Card: RTX 4080 SUPER under
# .local/gpu.lock; host part 8 threads; outer deadline 180 s.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap10; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap8/lap9/STATE.0
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/dev; rm -rf $D
$M dev timeout 180 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 3600000 60000 $D > $D.log 2>&1
grep -E '^FIELD_(STOPPED|KERNEL_ACCEPT|CARD )|^MEASURE|rror|panic' $D.log | cut -c1-400
grep '^FIELD_KERNEL lap' $D.log | python3 -I -c "
import sys
rows=[dict(kv.split('=') for kv in l.split()[1:]) for l in sys.stdin]
ms=sum(int(r['ms_section']) for r in rows); bl=sum(int(r['blocks']) for r in rows)
pr=[int(r['predicted_micro']) for r in rows]; tr=[int(r['transfer_micro']) for r in rows if r['transfer_micro']!='-']
ks=[int(r['k_star']) for r in rows]
print(f'sections={len(rows)} problems={16*len(rows)} blocks={bl} ms_a_problem={ms/(16*len(rows)):.2f} lap_projection_s={24685*ms/(16*len(rows))/1000:.0f} accept_milli_mean={sum(int(r[\"accept_milli\"]) for r in rows)/len(rows):.0f} k_star first {ks[:5]} last {ks[-5:]}')
"
echo "MAIN exit $(date -u +%H:%M:%S)"
