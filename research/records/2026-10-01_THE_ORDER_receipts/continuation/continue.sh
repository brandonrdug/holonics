#!/usr/bin/env bash
# Four guarded order-dec witness moves, each from the previous adopted continuing state; stops at a refusal.
set -u
state=research/records/2026-10-01_THE_ORDER_receipts/move/c6-witness.state
for k in 1 2 3 4; do
  out=.local/oc/m$k; mkdir -p $out
  bash research/notebook/hnn_design/read_probe.sh $out 519235 520 executed move-once order2 2026093061 8 $out m$k=$state order-dec witness
  status=$?
  echo "move $k: probe exit $status; $(tail -1 $out/identities.txt)"
  grep -E "^  m$k witness: (the adopted|refused)" $out/listing.txt | cut -c1-400
  [ -f $out/m$k-witness.state ] || { echo "move $k not adopted: stop"; break; }
  state=$out/m$k-witness.state
done
