#!/usr/bin/env bash
# The host part of a run's receipt (record 2026-10-31 §6): per lap and key file, the releases converted
# (card_written.py convert), the written rules, the never-met reads by operation and the carry, and the
# written coupling in both charts.   receipt.sh NAME CODEC
set -u
NAME=$1; CODEC=$2
W=$ROOT/.local/wt/bytes-1101
R=$ROOT/.local/wt/section-edge/.local/run; G=$R/gsm8k; E=$R/race/bytes-1101; O=$E/$NAME
SA=$W/target/release/examples/solenoidal_alpha
if [ $CODEC = units ]; then U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS; else U=$G/UNITS0; fi
grep -E '^TOWER_PASS ' $O.log | sed -E 's/ train_code=.*//'
for n in ${LAPS_READ:-10 20 30 40}; do
  echo "== lap $n"
  grep -h 'TOWER_RACE_FLUX prompt' $O-flux-$n.log 2>/dev/null | python3 -I -c '
import re,sys
t=0.0
for l in sys.stdin:
    for v in re.findall(r" \d+:(-?[\d.]+)", l.split("flux_bits_after_prompt")[1]): t+=float(v)
print(f"FLUX six questions whole answers summed = {t:.1f} bits")'
  for keys in GKEYS GKEYS_b GKEYS_c GKEYS_d; do
    D=$O-written-$n-$keys
    [ -d $D ] || (cd $G && python3 -I $W/tools/gsm8k/card_written.py convert $U $O-FREE-$n-$keys $O-MARKS-$n-$keys $D > /dev/null) || { echo "CONVERT failed $n $keys"; continue; }
    python3 -I $W/tools/gsm8k/written_rules.py $G/HELD128.txt $G/TRAIN.txt $D | sed "s#$E/##"
    python3 -I $W/.local/run/carry.py $W $G/HELD128.txt $G/TRAIN.txt $D | sed "s#$E/##"
    [ -f $D/COUPLING.tsv ] || $SA complete-language read-written-coupling $G/HELD128.txt $(sha256sum $G/HELD128.txt | cut -c1-64) $D | sed "s#^#$keys #"
  done
done
