#!/bin/bash
# lap 7 development reads (theory, November 7, 06:26: more evidence a step): contrast-field's kernel on the card from lap 5's
# STATE.0, one minute each at sections of 16, 64 and 256 states (the rate 12, 11 and 10; the moments counting states),
# to take the n with the least card time a state. Each read stops after the section past 60 s; the enumerated read at 64
# held places opens each. Card: RTX 4080 SUPER under .local/gpu.lock; host part 8 threads; outer deadline 180 s a read.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap7; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap4/lap5/STATE.0
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
for n in 16 64 256; do
  D=$O/dev$n; rm -rf $D
  $M dev$n timeout 180 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $n 1 64 3600000 60000 $D > $D.log 2>&1
  echo "== n=$n"; grep -E '^FIELD_(CONTRAST_DECL|STOPPED|KERNEL_ACCEPT|CARD )|^MEASURE|rror|panic' $D.log | cut -c1-260
  grep '^FIELD_KERNEL lap' $D.log | python3 -I -c "
import sys
rows=[dict(kv.split('=') for kv in l.split()[1:]) for l in sys.stdin]
ms=sum(int(r['ms_section']) for r in rows); st=sum(int(r['states']) for r in rows)
pr=[int(r['predicted_micro']) for r in rows]; tr=[int(r['transfer_micro']) for r in rows if r['transfer_micro']!='-']
print(f'n=$n sections={len(rows)} states={st} ms_a_state={ms/st:.2f} lap_projection_s={24685*ms/st/1000:.0f} predicted_micro_mean={sum(pr)/len(pr):.0f} transfer_micro_mean={(sum(tr)/len(tr)) if tr else 0:.0f}')
"
done
echo "MAIN exit $(date -u +%H:%M:%S)"
