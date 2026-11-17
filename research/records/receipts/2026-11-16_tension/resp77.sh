#!/bin/bash
# A receiver's response to each of its sources (the lead, November 17; guesses G-P1 and G-P2 fixed first): read-tension on the table of
# tools/response_ruler.py (8,000 short sums, each beside a perturbed copy a site) at lap 77's mean, then the ruler's read. On the host's
# threads beside the lap: no card, no state written. Projection: 163,000 places, about 13 minutes on 8 threads, the read's arithmetic a
# few minutes; deadline 2,400 s.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; B=$R/bin/athena_tension10; M=$Q/lap77/MEAN.2000; T=$R/resp77.tsv
sha() { sha256sum "$1" | cut -c1-64; }
env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 2400 $B host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/resp77 | grep -E 'TENSION_(LAW|DONE)|rror'
echo "# resp read exit $? $(date -u +%H:%M:%S)"
cd $ROOT/.local/wt/lead && python3 -I tools/response_ruler.py read $R/resp77 > $R/resp77.txt 2>&1
echo "# resp ruler exit $? $(date -u +%H:%M:%S)"
grep -E '^RESPONSE_(READ|PAIR)|^RESPONSE_MODES units [01] ' $R/resp77.txt | cut -c1-130
echo "RESP77 done $(date -u +%H:%M:%S)"
