#!/bin/bash
# The arithmetic world's held reads beside chain 23 (the laps after its gap, to 83; the lead, November 16), all from each lap's mean. On the host's threads (no card), once the
# lap's log holds its STORE_PASS line: the forms read (read-forms on the arithmetic table: the anchor's five forms and the held answers) and
# the writes after the arithmetic prompts (write-forms, 16 places). On the card, in the gap after the lap's own reads: the writes after 24
# GSM8K test questions (write-forms, 192 places; on the host's threads they passed 16 minutes on lap 70's mean and were stopped). The card
# write takes the card's lock as the lap releases it (asked while the lap holds it, so the chain, busy with its reads, is not yet waiting),
# holds it until the lap's loudness read has printed, then writes; the chain's next lap waits for it. Readings and writings: the states are
# read, never written. Six host threads beside the lap. Projection: the read 12 s, the arithmetic writes about 2.5 minutes on the host, the
# GSM8K writes about 30 s on the card (write-store wrote 20 problems of 256 places in 13.5 s); deadlines 600, 900 and 600 s.
set -u
ROOT=ROOT; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line; O=$Q/forms
D=$ROOT/.local/corpus/store-2026-11-16; B=$ROOT/.local/wt/depth-sweep/.local/run/mark/bin/athena_acts
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; FA=$D/FORMS_arithmetic5.tsv; FG=$D/FORMS_gsm8k.tsv; LOCK=$ROOT/.local/gpu.lock
sha() { sha256sum "$1" | cut -c1-64; }
host() { env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=6 timeout "$@"; }
for n in $(seq $(($1 + 1)) 83); do
  until grep -q "^# lap$n: lock taken" $Q/line-twenty-three.out 2>/dev/null || grep -q '^MAIN' $Q/line-twenty-three.out 2>/dev/null; do sleep 20; done
  grep -q "^# lap$n: lock taken" $Q/line-twenty-three.out || { echo "FORMS STOP lap$n never took the lock"; exit 1; }
  (
    flock -w 7200 9 || exit 75
    grep -qE '^STORE_PASS |^STORE_STOPPED ' $Q/lap$n.log || { echo "FORMS STOP lap$n has no pass or stop line"; exit 1; }
    m=$(ls $Q/lap$n/MEAN.* | sort -t. -k2 -n | tail -1)
    (
      host 600 $B host complete-language read-forms $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $FA $(sha $FA) $m $(sha $m) > $O/forms$n.log 2>&1
      python3 -I $ROOT/.local/wt/arithworld/tools/forms_table.py sum $FA $O/forms$n.log > $O/forms$n.sum 2>&1
      echo "# forms$n $(date -u +%H:%M:%S): $(grep -E '^FORMS_DONE|rror' $O/forms$n.log | cut -c1-120)"
      host 900 $B host complete-language write-forms $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $FA $(sha $FA) 16 $O/wf$n $m $(sha $m) > $O/wf$n.log 2>&1
      echo "# wf$n $(date -u +%H:%M:%S): $(grep -E '^FORMS_WRITE_DONE|rror' $O/wf$n.log | cut -c1-120)"
    ) &
    until grep -q "^# loud$n:" $Q/line-twenty-three.out 2>/dev/null || grep -q '^MAIN' $Q/line-twenty-three.out 2>/dev/null; do sleep 5; done
    sleep 3
    env -i HOME=$HOME PATH=$PATH timeout 600 $B train complete-language write-forms $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $FG $(sha $FG) 192 $O/wg$n $m $(sha $m) > $O/wg$n.log 2>&1
    echo "# wg$n $(date -u +%H:%M:%S): $(grep -E '^FORMS_WRITE_DONE|rror' $O/wg$n.log | cut -c1-120)"
    wait
  ) 9>$LOCK
done
echo "FORMS done $(date -u +%H:%M:%S)"
