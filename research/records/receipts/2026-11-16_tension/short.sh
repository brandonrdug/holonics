#!/bin/bash
# Short sums read alone at a lap's mean (the lead, November 16): read-tension on short76.tsv (sums of one- and two-digit operands, a record a
# region, every answer place opened alone) with every site written, for the code by part, the operands' presence and the rows' heat. The
# instrument G-V1 and G-V2 are scored with. A reading on the host's threads beside the lap: no card, no state. Projection: 8,000 regions of
# about 14 sites, a few minutes on 8 threads; deadline 1,200 s.
set -u
N=$1
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; B=$R/bin/athena_tension9; T=$R/short76.tsv
M=$(ls $Q/lap$N/MEAN.* | sort -t. -k2 -n | tail -1)
sha() { sha256sum "$1" | cut -c1-64; }
echo "# short$N on ${M#$Q/} $(date -u +%H:%M:%S) threads=8"
# Two reads: the open places alone (the oracle's rows, as short76 was read) and every site (the rows' shares, for the heat).
for form in o a; do
  [ -e $R/short$N$form ] && continue
  env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 1200 $B host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/short$N$form $([ $form = a ] && echo all) | grep -E 'TENSION_(LAW|DONE)|rror'
  echo "SHORT$N$form exit $? $(date -u +%H:%M:%S)"
done
cd $ROOT/.local/wt/lead
python3 -I tools/tension_ruler.py oracle $R/short${N}o > $R/oracle_short$N.txt 2>&1; echo "# oracle $? $(date -u +%H:%M:%S)"
python3 -I tools/tension_ruler.py heat $R/short${N}a > $R/heat_short$N.txt 2>&1; echo "# heat $? $(date -u +%H:%M:%S)"
grep -E '^TENSION_CODE met \+|^TENSION_PRESENCE met ' $R/oracle_short$N.txt | cut -c1-120
grep -E '^TENSION_HEAT met 0 ' $R/heat_short$N.txt | cut -c1-160
