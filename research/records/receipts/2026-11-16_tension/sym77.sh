#!/bin/bash
# A held passage under two changes of frame (the lead, November 17; guesses G-Y0 to G-Y2 fixed first): read-tension on the plain, renamed
# and doubled tables of tools/symbol_frame_ruler.py at lap 77's mean. Readings on the host's threads beside lap 78: no card, no state
# written. Projection: about 2.5 minutes each for the plain and renamed tables and about 9 for the doubled one on 8 threads; deadline
# 1,800 s a read.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; B=$R/bin/athena_tension10; M=$Q/lap77/MEAN.2000
sha() { sha256sum "$1" | cut -c1-64; }
for frame in plain renamed doubled; do
  T=$R/sym77.$frame.tsv
  env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 1800 $B host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/sym77_$frame | grep -E 'TENSION_(LAW|DONE)|rror'
  echo "# sym $frame exit $? $(date -u +%H:%M:%S)"
done
cd $ROOT/.local/wt/lead && python3 -I tools/symbol_frame_ruler.py read $R/sym77_plain $R/sym77_renamed $R/sym77_doubled > $R/sym77.txt 2>&1
cat $R/sym77.txt
echo "SYM77 done $(date -u +%H:%M:%S)"
