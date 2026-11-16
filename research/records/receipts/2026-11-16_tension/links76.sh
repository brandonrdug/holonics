#!/bin/bash
# The way of an operand digit to the answer's place, link by link (the lead's read of November 16, after the tension read found the operands
# faint at the junction): fresh sums and differences (3,000 at met lengths, 600 far, two value digits a record opened alone), every site of
# each region written at every tick with the tick's opening chart, the pair chart, the current and the open row's shares by head. A reading
# on the host's threads beside the card: no card, no state written. Projection: 7,200 regions at about 120 a second on 8 threads, about 60 s
# of reads and about 1.5 GB written; the deadline 900 s.
set -u
ROOT=ROOT; R=$ROOT/.local/wt/lead/.local/run/tension; Q=$ROOT/.local/wt/depth-sweep/.local/run/mark/lane/line
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0; K=$ROOT/.local/wt/field-card/.local/run/KEYS8
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; T=$R/links76.tsv
M=$(ls $Q/lap76/MEAN.* | sort -t. -k2 -n | tail -1)
sha() { sha256sum "$1" | cut -c1-64; }
echo "# state ${M#$Q/}"
env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=8 timeout 900 $R/bin/athena_tension3 host complete-language read-tension $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $T $(sha $T) $M $(sha $M) $R/links76 all
echo "LINKS76 exit $? $(date -u +%H:%M:%S)"
