#!/bin/bash
# A turned head cooled on short sums (the lead, November 16; guesses G-H1 to G-H5 fixed first): ruler states of lap 77's mean with head 3's
# listener temperature raised by two octaves and by one, each read with the instrument of G-V (the open places alone for the oracle, every
# site for the heat), ten located products, and the held passage at 100 places a slice. Readings on the host's threads beside lap 78: no
# card, no line state written. Projection: two reads of about 80 s, the located products a few minutes, the held read about 75 s, for each
# of two states; deadlines 1,200 s a read.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8; S=$ROOT/.local/corpus/store-2026-11-16
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; B=$R/bin/athena_tension10; T=$R/short76.tsv; M=$Q/lap77/MEAN.2000
sha() { sha256sum "$1" | cut -c1-64; }
host() { env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout "$@"; }
cd $ROOT/.local/wt/lead
for milli in 2000 1000; do
  X=$R/cool77_$milli
  [ -e $X.state ] || $B train complete-language ruler-temper $M $(sha $M) 3 $milli $X.state | grep RULER_TEMPER
  for form in o a; do
    host 1200 $B host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $X.state $(sha $X.state) $X$form $([ $form = a ] && echo all) | grep -E 'TENSION_(LAW|DONE|TEMPER)|rror'
  done
  python3 -I tools/tension_ruler.py oracle ${X}o > $X.oracle.txt 2>&1; python3 -I tools/tension_ruler.py heat ${X}a > $X.heat.txt 2>&1
  echo "# cool $milli oracle and heat $(date -u +%H:%M:%S)"
  grep -E '^TENSION_CODE met \+ (units|top)|^TENSION_PRESENCE met [01] ' $X.oracle.txt | cut -c1-110; grep -E '^TENSION_HEAT met 0 3 ' $X.heat.txt | cut -c1-150
  python3 -I tools/tension_ruler.py located ${X}o 10 > $X.located.txt 2>&1; echo "# cool $milli located $(date -u +%H:%M:%S)"
  grep -E '^TENSION_LOCATED_PART met [01] units|^TENSION_LOCATED met [01] 10 ' $X.located.txt | cut -c1-120
  host 1800 $B host complete-language read-cavity $U0 $(sha $U0) $S $(sha $S/STORE.tsv) $K $(sha $K) $C $(sha $C) 100 $X.state $(sha $X.state) ${X}_cav > $X.cav.log 2>&1
  echo "# cool $milli held $(date -u +%H:%M:%S) $(grep -c CAVITY_SLICE $X.cav.log) slices"
done
echo "COOL77 done $(date -u +%H:%M:%S)"
