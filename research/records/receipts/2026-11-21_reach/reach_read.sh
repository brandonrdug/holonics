#!/bin/bash
# The reach's premise read (the lead, November 21): the code of every place by two streams at W79t's lap mean under a ruler's friction of
# distance on the still heads' listeners, on the terrain's records (rows.tsv) and on the 800 held frontier rows of text (far_rows.tsv).
# Host only, 12 threads; the card idle. Projection: about 6 settings x (40 + 50) s, 9 minutes; deadline 1,500 s each table.
ROOT=${ROOT:?the main checkout}; K=$ROOT/.local/wt/field-card/.local/run/KEYS8; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
C=$ROOT/.local/wt/store-trainer/.local/run/p48/g115r1/CODEC; M=${STATE:-$ROOT/.local/wt/lead/.local/run/front/arm_W79t/MEAN.3000}
TXT=$ROOT/.local/wt/lead/.local/run/front/far/far_rows.tsv; TAG=${TAG:-W79t}
sha() { sha256sum "$1" | cut -c1-64; }
S="law 0:1:500 0:1:1000 0:1:2000 0:1:1000,1:1:1000 2:1:1000,3:1:1000"
for t in terrain text; do
  R=rows.tsv; [ $t = text ] && R=$TXT
  rm -rf code_${t}_$TAG
  env -i HOME=$HOME PATH=$PATH RAYON_NUM_THREADS=12 timeout 1500 ./athena host complete-language read-reach $U0 $(sha $U0) $K $(sha $K) $C $(sha $C) $R $(sha $R) $M $(sha $M) code_${t}_$TAG $S > code_${t}_$TAG.log 2>&1
  echo "REACH_TABLE $t exit=$? $(date -u +%H:%M:%S)"; grep -E "group=all|rror|efus" code_${t}_$TAG.log
done
