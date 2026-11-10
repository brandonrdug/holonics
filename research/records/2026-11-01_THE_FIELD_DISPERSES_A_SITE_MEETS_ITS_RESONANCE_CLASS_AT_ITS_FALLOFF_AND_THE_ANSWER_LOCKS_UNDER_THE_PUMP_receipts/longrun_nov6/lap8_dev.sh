#!/bin/bash
# lap 8 development read (theory, November 7, 06:57: each family reads its length from its own transfer; the letters'
# temperature joins the deposit): (1) the held enumerated code from lap 5's state at log2 T moved by -1/2 and -1, untrained
# (LAPS 0); (2) one minute of lap 8's law at 16 states a section. Card: RTX 4080 SUPER under .local/gpu.lock; host part 8
# threads; outer deadline 180 s a read.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap8; BIN=$O/field_pass
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$R/2026-11-07-lap4/lap5/STATE.0
ARGS="$S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16"
exec 9>$ROOT/.local/gpu.lock; flock -w 900 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
for shift in -500 -1000; do
  D=$O/held$shift; rm -rf $D
  FIELD_CONTRAST_LOG2T_SHIFT_MILLI=$shift $M held$shift timeout 180 $BIN train complete-language contrast-field $ARGS 0 64 3600000 60000 $D > $D.log 2>&1
  echo "== log2 T shift $shift milli"; grep -E '^FIELD_CONTRAST_LOG2T|^MEASURE|rror|panic' $D.log | cut -c1-200
  python3 -I $O/enumerated.py $D/ENUMERATED.tsv | head -3
done
D=$O/dev; rm -rf $D
$M dev timeout 180 $BIN train complete-language contrast-field $ARGS 1 64 3600000 60000 $D > $D.log 2>&1
echo "== lap 8 law, one minute"; grep -E '^FIELD_(STOPPED|KERNEL_ACCEPT|KERNEL_TENTH|CARD )|^MEASURE|rror|panic' $D.log | cut -c1-900
grep '^FIELD_KERNEL lap' $D.log | python3 -I -c "
import sys
rows=[dict(kv.split('=') for kv in l.split()[1:]) for l in sys.stdin]
ms=sum(int(r['ms_section']) for r in rows); st=sum(int(r['states']) for r in rows)
pr=[int(r['predicted_micro']) for r in rows]; tr=[int(r['transfer_micro']) for r in rows if r['transfer_micro']!='-']
print(f'sections={len(rows)} ms_a_state={ms/st:.2f} lap_projection_s={24685*ms/st/1000:.0f} predicted_micro_mean={sum(pr)/len(pr):.0f} transfer_micro_mean={(sum(tr)/len(tr)) if tr else 0:.0f} log2_t_first={rows[0][\"log2_t\"]} last={rows[-1][\"log2_t\"]}')
"
echo "MAIN exit $(date -u +%H:%M:%S)"
