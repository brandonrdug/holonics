#!/usr/bin/env bash
# Copy a run's count-only receipts into the record's receipts directory, machine paths replaced by $ROOT.
#   collect.sh NAME...   (r0, r1, r2, r1-stopped, r1dev, r2dev, parity77-*, suite77)
set -u
W=$ROOT/.local/wt/bytes-1101; E=$ROOT/.local/wt/section-edge/.local/run/race/bytes-1101
D=$W/research/records/2026-10-31_A_QUESTIONS_NUMBER_IS_ANOTHER_WORD_IN_ITS_CALCULATION_SO_THE_CODEC_BLOCKS_THE_COPY_AND_THE_GATED_MODES_HOLD_NO_CARRY_receipts/bytes-1101
mkdir -p $D
clean() { sed -e "s#$ROOT#\$ROOT#g" -e "s#<scratch> ]*#<scratch>#g" "$1" > "$2"; }
for n in "$@"; do
  case $n in parity77-*|suite77) [ -f $E/$n.log ] && clean $E/$n.log $D/$n.txt;; *) [ -f $E/$n.log ] && clean $E/$n.log $D/$n-train.txt;; esac
  for lap in 5 10 20 30 40; do [ -f $E/$n-flux-$lap.log ] && clean $E/$n-flux-$lap.log $D/$n-flux-$lap.txt; done
  [ -f $W/.local/run/$n.txt ] && clean $W/.local/run/$n.txt $D/$n.txt
  if [ -f $W/.local/run/$n-receipt.txt ]; then
    clean $W/.local/run/$n-receipt.txt $D/$n-receipt.txt
    python3 -I $W/.local/run/summarize.py $W/.local/run/$n-receipt.txt > $D/$n-summary.txt
  fi
done
for s in brun.sh receipt.sh carry.py summarize.py dev.sh p77b.sh collect.sh; do clean $W/.local/run/$s $D/$s; done
ls $D | wc -l
