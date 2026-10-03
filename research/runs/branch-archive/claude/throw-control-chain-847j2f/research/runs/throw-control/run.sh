#!/usr/bin/env bash
# The throw's control chain: the throw's own run.sh
# (research/records/2026-10-02_THE_THROW_receipts/run.sh at b1d37a84) with `coordinate` in place of
# `throw`. Same opening c0, same batch (order2, seed 2026093061, 8 requests), arm lock-dec,
# EXCURSION_CHECKPOINT unset (so move_once releases under ReleaseExcursion::monotone(): strict descent
# of the released code length against the incumbent), up to 16 moves. The Coordinate step carries no
# flight, so every move starts at rest and a refused move ends the chain, as a refusal at rest ends
# the throw's.
#
#   RAYON_NUM_THREADS=4 bash research/runs/throw-control/run.sh <out root> <per-move ms> <per-move s> [<moves>]
set -u
unset EXCURSION_CHECKPOINT
root=${1:?an output root}
unit=${2:?the per-move bound in ms}
deadline=${3:?the per-move deadline in s}
moves=${4:-16}
state=research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state
for k in $(seq 0 $((moves - 1))); do
  out=$root/m$k; mkdir -p "$out"
  cp "$state" "$out/in.state"
  bash research/notebook/hnn_design/read_probe.sh "$out" "$unit" "$deadline" \
    executed move-once order2 2026093061 8 "$out" m$k="$out/in.state" lock-dec coordinate
  status=$?
  echo "move $k: probe exit $status; $(tail -1 "$out/identities.txt")"
  grep -E "^  m$k coordinate: (the incumbent|the adopted|refused)|^    move 0:|^      trials:" "$out/listing.txt" | cut -c1-300
  if [ $status -ne 0 ]; then echo "move $k incomplete: stop"; break; fi
  if [ -f "$out/m$k-coordinate.state" ]; then
    state=$out/m$k-coordinate.state
  else
    echo "move $k refused at rest: stop"
    break
  fi
done
echo "run done"
