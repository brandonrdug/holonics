#!/usr/bin/env bash
# The kinetic chain under the run-of-moves acceptance: each move's held-sheet comparison must fall
# (the move's own law); the released comparison is compared only at the endpoints of a run, which
# closes when its end lies below its held state by σ (closes.py). A run that does not close within W
# moves, a refused move inside an open run, and the overall limit reached inside an open run all
# return the chain to the held state, read back from its own file and checked byte for byte.
#   METRIC=<kinetic|kinetic-modulus|coordinate|witness> [UNIT_MS=… DEADLINE_S=… RAYON_NUM_THREADS=…] \
#     bash research/runs/u6/chain.sh <start state> <label> <out dir> <max moves> <W> 0/1 0/1
# Run from the repository root; the binary is ${CARGO_TARGET_DIR:-target}/release/examples/hnn_prediction.
# σ = 64 decisions · 1/16 · ln 2 at an upper rational end of ln 2 (closes.py), the same σ as
# `executed run`'s header.
set -u
start=$1; label=$2; outdir=$3; MAX=$4; W=$5
METRIC=${METRIC:-kinetic}
export DECISION_DIFF=1
UNIT_MS=${UNIT_MS:-630263}; DEADLINE_S=${DEADLINE_S:-631}
state=$start; checkpoint="$6 $7"; first=1; window=0
held=$start; heldsum=$(sha256sum "$start" | cut -d' ' -f1)
restore() {
  now=$(sha256sum "$held" | cut -d' ' -f1)
  [ "$now" = "$heldsum" ] && echo "  restored the held state $held (sha256 $heldsum, unchanged)" || echo "  RESTORE FAILED: $held changed ($heldsum -> $now)"
  state=$held
}
for k in $(seq 1 $MAX); do
  out=$outdir/$label$k; mkdir -p $out
  export EXCURSION_CHECKPOINT="$checkpoint"
  bash research/notebook/hnn_design/read_probe.sh $out $UNIT_MS $DEADLINE_S executed move-once order2 2026093061 8 $out $label$k=$state lock-dec $METRIC
  rc=$?
  inc=$(grep -m1 "the incumbent's own comparison, exact" $out/listing.txt | sed 's/.*exact: //')
  [ $first = 1 ] && [ -n "$inc" ] && { checkpoint="$inc"; first=0; echo "held state's released comparison, exact: $checkpoint"; }
  echo "move $k: probe exit $rc; $(grep -E "^  $label$k $METRIC: (the incumbent|refused)" $out/listing.txt | cut -c1-200)"
  grep -E "^      trials:" $out/listing.txt | cut -c1-400
  if [ ! -f $out/$label$k-$METRIC.state ]; then
    echo "move $k not accepted (probe exit $rc)"; [ $window -gt 0 ] && restore; break
  fi
  own=$(grep -m1 "the successor's own comparison, exact" $out/listing.txt | sed 's/.*exact: //')
  window=$((window+1))
  verdict=$(python3 research/runs/u6/closes.py ${checkpoint% *} ${own#* })
  echo "  run move $window: $(grep -m1 "adopted successor's own release" $out/listing.txt | cut -c30-260); $verdict"
  state=$out/$label$k-$METRIC.state
  if [ "$verdict" = closes ]; then
    checkpoint="$own"; held=$state; heldsum=$(sha256sum "$held" | cut -d' ' -f1); window=0; echo "  the run closes; held state now $held"
  elif [ $window -ge $W ]; then
    echo "  the run did not close in $W moves"; restore; break
  fi
done
[ $window -gt 0 ] && [ "$state" != "$held" ] && { echo "  the limit was reached inside an open run"; restore; }
echo "final state $state"
echo "run done"
