#!/bin/bash
# lap 13 (theory, November 7, 09:36): the field meets 16 persistent writes (one a problem slot, started once from the joint
# release, never restarted; each section's write j takes its j-th question at its true length; the energy's sweep moves
# one residue class of its places at T, one read a position), the deposit (1/T) sum [dG/dtheta(truth) - dG/dtheta(write)],
# T learning and the family lengths carried; from the k = 4 lap's end. A one-minute development read projects the lap; the
# deadline is 1.25x that plus the enumerated reads; then the 8 prompts written from the lap's state. Overnight runs
# pre-authorized (Brandon, November 7 08:10). Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads.
set -u
export RAYON_NUM_THREADS=8 FIELD_CONTRAST_PERSISTENT=1
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap13; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-pin4/lap/STATE.0
ARGS="$S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64"
exec 9>$ROOT/.local/gpu.lock; flock 9
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/dev; rm -rf $D
$M dev timeout 300 $BIN train complete-language contrast-field $ARGS 3600000 60000 $D > $D.log 2>&1
grep -E '^FIELD_(STOPPED|PERSISTENT_LAP)|^MEASURE|rror|panic' $D.log | cut -c1-300; grep '^FIELD_PERSISTENT lap' $D.log | awk 'NR<=3 || NR%20==0' | cut -c1-300
PROJ=$(grep '^FIELD_PERSISTENT lap' $D.log | python3 -I -c "
import sys
rows=[dict(kv.split('=') for kv in l.split()[1:]) for l in sys.stdin]
ms=sum(int(r['sweep_ms'])+int(r['deposit_ms']) for r in rows)
print(int(1543*ms/len(rows)))")
DEAD=$(( PROJ * 5 / 4 + 30000 ))
echo "# projection ${PROJ} ms, deadline ${DEAD} ms"
D=$O/lap; rm -rf $D
$M lap timeout $(( DEAD / 1000 + 200 )) $BIN train complete-language contrast-field $ARGS $DEAD $DEAD $D > $D.log 2>&1
grep -E '^FIELD_(PERSISTENT_LAP|STOPPED|CARD |ENUMERATED_READ)|^MEASURE|rror|panic' $D.log | cut -c1-400
grep '^FIELD_PERSISTENT lap' $D.log | awk 'NR%150==1' | cut -c1-300
[ -f $D/ENUMERATED.tsv ] && python3 -I $O/enumerated.py $D/ENUMERATED.tsv && python3 -I $O/singular.py $D/ENUMERATED.tsv $F84/dev/CODEC 0 | head -2
ST=$D/STATE.0; [ -f $ST ] || ST=$D/STATE.stopped
echo "STATE $(sha $ST)"
W=$O/write; rm -rf $W
unset FIELD_CONTRAST_PERSISTENT
timeout 3400 $BIN train complete-language kernel-write $ST $(sha $ST) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 8 128 2831412 $W > $W.log 2>&1
echo "write rc $?"; grep -E '^FIELD_WRITE_(ENERGY|EQUILIBRIUM|DONE)|rror|panic' $W.log | cut -c1-300
echo "MAIN exit $(date -u +%H:%M:%S)"
