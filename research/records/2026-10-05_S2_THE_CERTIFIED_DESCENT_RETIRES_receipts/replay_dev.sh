#!/usr/bin/env bash
# The kept release path read again on the pair gain record's development seed (8 requests, both keys
# states, each terrain), its section listing diffed against that record's receipt. Projection: the
# release build within 600 s; each read 12,381 ms at most (the receipt's largest), deadline 120 s.
set -u
export CARGO_TARGET_DIR=$PWD/target
s=$(date +%s%3N); timeout 600 cargo build --release -q -p holonics --example hnn_prediction -j 12; echo "build exit $? wall $(( $(date +%s%3N) - s )) ms"
bin=$CARGO_TARGET_DIR/release/examples/hnn_prediction
keys=research/records/2026-10-05_LOCATED_KEYS_receipts
reg=research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE_receipts
gain=research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT_receipts/development
for t in order2 alternation line; do
  if [ $t = order2 ]; then st="keys-founded=$keys/state_keys_founded.txt keys-lossless=$keys/state_keys_lossless.txt";
  else st="keys-founded=$reg/state_${t}_keys_founded.txt keys-lossless=$reg/state_${t}_keys_lossless.txt"; fi
  s=$(date +%s%3N)
  RAYON_NUM_THREADS=12 timeout 120 $bin executed evaluate $t 2026093042 8 .local/receipts/eval_dev_${t}_sections.txt $st > .local/receipts/eval_dev_${t}_log.txt 2>&1
  echo "$t exit $? wall $(( $(date +%s%3N) - s )) ms"
  cmp -s .local/receipts/eval_dev_${t}_sections.txt $gain/eval_dev_${t}_sections.txt && echo "$t sections: identical to the receipt" || echo "$t sections: DIFFER"
  diff <(sed -E 's/; [0-9]+ ms$//' .local/receipts/eval_dev_${t}_log.txt | grep -v '^executed evaluate:') <(sed -E 's/; [0-9]+ ms$//' $gain/eval_dev_${t}_log.txt | grep -v '^executed evaluate:') > /dev/null && echo "$t counts: identical outside the wall times" || echo "$t counts: DIFFER"
done
