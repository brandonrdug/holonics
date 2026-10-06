#!/usr/bin/env bash
# The reproduction acceptance (lane E, phase 2): #375's validation reads on the keys states written
# again, each under its committed pin (research/runs/states-written-again/, guard 22), at this build.
set -u
bin=./target/release/examples/hnn_prediction
receipts=research/records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE_receipts/written_again
out=.local/repro
pins=research/runs/states-written-again
pin() {
  local f=$pins/$1
  git ls-files --error-unmatch -- "$f" > /dev/null 2>&1 || { echo "refused: $f is not committed" >&2; exit 3; }
  git diff --quiet HEAD -- "$f" || { echo "refused: $f differs from its commit" >&2; exit 3; }
  [ "$(git log --format=%H -- "$f" | wc -l)" = 1 ] || { echo "refused: $f was committed more than once" >&2; exit 3; }
  sed -n "s/^$2 = //p" "$f"
}
mkdir -p $out
for t in "order2 2026093032" "alternation 2026093035" "line 2026093038"; do
  set -- $t
  ms=$(pin evaluate-validation-$1.pin deadline_ms); threads=$(pin evaluate-validation-$1.pin threads)
  log=$out/validation_$1_log.txt
  start=$(date +%s%3N)
  systemd-run --user --wait --collect -p MemoryAccounting=yes --working-directory="$PWD" \
    -E RAYON_NUM_THREADS="$threads" \
    -p StandardOutput=truncate:"$PWD/$log" -p StandardError=append:"$PWD/$log" -- \
    bash -c '"$@"; s=$?; echo "--- scope: exit $s; memory.peak $(cat /sys/fs/cgroup$(grep "^0::" /proc/self/cgroup | cut -d: -f3)/memory.peak) bytes"; exit $s' _ \
    timeout $(( ms / 1000 )) $bin executed evaluate $1 $2 64 $out/validation_$1_sections.txt \
      keys-founded=$receipts/state_$1_keys_founded.txt keys-lossless=$receipts/state_$1_keys_lossless.txt 2>&1 \
    | grep -E "terminated|runtime|CPU" >> "$log"
  echo "wall $(( $(date +%s%3N) - start )) ms (pin deadline $ms ms, threads $threads)" >> "$log"
  cmp -s $out/validation_$1_sections.txt $receipts/validation_$1_sections.txt \
    && echo "$1: validation sections byte-identical to #375's receipt" \
    || echo "$1: validation sections DIFFER from #375's receipt"
done | tee $out/compare.txt
