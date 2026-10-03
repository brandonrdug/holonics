#!/usr/bin/env bash
# The throw's chain from the opening (the throw's record §6): up to 16 successive
# `move-once … lock-dec throw` moves on gate A's batch, each from the last adopted state and its flight.
# A refused move with a carried coast ends the flight: the next move starts from the same state at rest.
# A refused move at rest ends the chain.
#
#   [RAYON_NUM_THREADS=<n>] bash research/records/2026-10-02_THE_THROW_receipts/run.sh <out root> <per-move ms> <per-move s> [<moves>]
#
# <moves> is 16 by default; the development read passes 2 (the release m0 and the first coast m1).
# The per-move bound is the projection's upper end: the largest measured move of the development read
# (m0 at rest, m1 with its first coast), fixed before launch and never raised (the waiting standard).
set -u
root=${1:?an output root, e.g. .local/throw}
unit=${2:?the per-move bound in ms}
deadline=${3:?the per-move deadline in s}
moves=${4:-16}
state=research/records/2026-10-01_THE_GUARDED_WITNESS_receipts/c0.state
flight=""
for k in $(seq 0 $((moves - 1))); do
  out=$root/m$k; mkdir -p "$out"
  # The flight rides beside the state as `<state>.flight`; at rest there is none.
  if [ -n "$flight" ]; then cp "$flight" "$out/in.state.flight"; fi
  cp "$state" "$out/in.state"
  bash research/notebook/hnn_design/read_probe.sh "$out" "$unit" "$deadline" \
    executed move-once order2 2026093061 8 "$out" m$k="$out/in.state" lock-dec throw
  status=$?
  echo "move $k: probe exit $status; $(tail -1 "$out/identities.txt")"
  grep -E "^  m$k throw: (the incumbent|the adopted|refused)|the throw:" "$out/listing.txt" | cut -c1-300
  if [ $status -ne 0 ]; then echo "move $k incomplete: stop"; break; fi
  if [ -f "$out/m$k-throw.state" ]; then
    state=$out/m$k-throw.state
    flight=$out/m$k-throw.state.flight
  elif [ -n "$flight" ]; then
    echo "move $k refused in flight: the next move starts from rest"
    flight=""
  else
    echo "move $k refused at rest: stop"
    break
  fi
done
echo "run done"
