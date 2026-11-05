#!/bin/bash
# §16.44's reading (1) and the acceptance on three states once exact63's segment 1 is written: main52 seg3 STATE.10 (the
# blank law untrained), blank60 seg1 STATE.8 (the operand form) and exact63 seg1's last state (the exact return), each
# restate-field with the gap's clocks by tick, then clocks_read.py and acceptance.py. Projection: 80 s a state (accept61's
# law read 70 s, plus 393 clock reads), 240 s; deadline 240 s each. RTX 4080 SUPER under .local/gpu.lock (one window
# between exact63's steps), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; R=$W/.local/run; O=$R/2026-11-05-clocks64
D=$W/research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP_receipts/law60
timeout 7200 bash -c "until grep -q '^SEGMENT 1 done' $R/2026-11-05-exact63/launch.out; do sleep 10; done"
timeout 1800 bash -c "until grep -q 'PARITY exit' $O/parity.out; do sleep 10; done"
grep -q 'learners_unequal=0 releases=1 releases_unequal=0' $O/parity.out && ! grep -q 'clocks_equal=false' $O/parity.out || { echo "READS clocks parity failed"; exit 1; }
E=$(ls -t $R/2026-11-05-exact63/seg1/STATE.* | grep -v stopped | head -1)
bash $R/2026-11-05-accept61/trio.sh clocksun $O/field_pass $R/2026-11-04-main52/seg3/STATE.10
bash $R/2026-11-05-accept61/trio.sh clocksop $O/field_pass $R/2026-11-04-blank60/seg1/STATE.8
bash $R/2026-11-05-accept61/trio.sh clocksex $O/field_pass $E
for tag in clocksun-seg3-STATE.10 clocksop-seg1-STATE.8 clocksex-seg1-$(basename $E); do
  [ -f $R/2026-11-05-accept61/$tag/CLOCKS.tsv ] && python3 -I $D/clocks_read.py $R/2026-11-05-accept61/$tag/CLOCKS.tsv
done
echo "READS exit $(date -u +%H:%M:%S)"
