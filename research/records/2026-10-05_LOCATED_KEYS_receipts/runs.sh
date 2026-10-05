#!/usr/bin/env bash
# Lane B's runs (research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md),
# each run once, from the worktree root, at the build of the record's commit. Thread budget 8.
# The final confirmation seeds (2_026_093_033, 036, 039) are named nowhere: no run reads them.
set -u
bin=./target/release/examples/hnn_prediction
out=research/records/2026-10-05_LOCATED_KEYS_receipts
# Development (readable seeds 2_026_093_041 and 042): the keys, then the release on other requests.
timeout 120 $bin executed keys order2 2026093041 16 .local/dev/keys_dev
RAYON_NUM_THREADS=8 timeout 600 $bin executed evaluate order2 2026093042 8 .local/dev/eval_dev_sections.txt \
  lossless opening keys-lossless=.local/dev/keys_dev.lossless keys-founded=.local/dev/keys_dev.founded
for s in 1/2 4; do timeout 120 $bin executed keys-probe order2 2026093041 16 $s .local/dev/probe_${s/\//_}; done
RAYON_NUM_THREADS=8 timeout 600 $bin executed evaluate order2 2026093042 8 .local/dev/eval_probe_sections.txt \
  p12-lossless=.local/dev/probe_1_2.lossless p12-founded=.local/dev/probe_1_2.founded \
  p4-lossless=.local/dev/probe_4.lossless p4-founded=.local/dev/probe_4.founded
# The machine's training passages (the two counts' seeds): the readings to lock, and the deposit.
for t in "order2 2026093031" "alternation 2026093034" "line 2026093037"; do
  set -- $t
  timeout 120 $bin executed keys $1 $2 128 .local/runs/keys_$1 > $out/keys_$1_log.txt 2>&1
done
timeout 120 $bin executed keys-probe order2 2026093031 128 4 .local/runs/probe_4
# The validation read (2_026_093_032, 64 requests): projection 505,000 ms, deadline 660,000 ms.
RAYON_NUM_THREADS=8 timeout 660 $bin executed evaluate order2 2026093032 64 $out/validation_order2_sections.txt \
  lossless opening keys-lossless=.local/runs/keys_order2.lossless keys-founded=.local/runs/keys_order2.founded \
  probe-founded=.local/runs/probe_4.founded > $out/validation_order2_log.txt 2>&1
