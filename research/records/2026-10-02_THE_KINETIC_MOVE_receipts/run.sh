#!/usr/bin/env bash
set -u
state=research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state
for k in 0 1 2 3 4 5 6 7; do
  out=.local/km/m$k; mkdir -p $out
  bash research/notebook/hnn_design/read_probe.sh $out 630263 631 executed move-once order2 2026093061 8 $out m$k=$state lock-dec kinetic
  echo "move $k: probe exit $?; $(tail -1 $out/identities.txt)"
  grep -E "^  m$k kinetic: (the incumbent|the adopted|refused)|the receiver's solve" $out/listing.txt | cut -c1-300
  [ -f $out/m$k-kinetic.state ] || { echo "move $k not adopted: stop"; break; }
  state=$out/m$k-kinetic.state
done
echo "run done"
