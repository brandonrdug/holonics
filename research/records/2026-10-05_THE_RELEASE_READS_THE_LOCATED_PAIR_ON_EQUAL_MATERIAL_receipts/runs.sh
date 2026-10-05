#!/usr/bin/env bash
# Lane C's runs (research/records/2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL.md),
# each run once, from the worktree root, at the build of the record's commit. Thread budget 12.
# The states are lane B's, unchanged (research/records/2026-10-05_LOCATED_KEYS_receipts/).
# The final confirmation seeds (2_026_093_033, 036, 039) are named nowhere: no run reads them.
set -u
bin=./target/release/examples/hnn_prediction
keys=research/records/2026-10-05_LOCATED_KEYS_receipts
out=research/records/2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL_receipts
# Development (seed 2_026_093_042, 8 requests): the keys states, then the openings (lane B's listing
# reproduced), and the members along the target's trajectory on the first request.
RAYON_NUM_THREADS=12 timeout 120 $bin executed evaluate order2 2026093042 8 $out/development/pair_dev_sections.txt \
  keys-founded=$keys/state_keys_founded.txt keys-lossless=$keys/state_keys_lossless.txt
RAYON_NUM_THREADS=12 timeout 120 $bin executed evaluate order2 2026093042 8 $out/development/open_dev_sections.txt lossless opening
timeout 120 $bin executed pair-members order2 2026093042 1 $keys/state_keys_founded.txt > $out/development/pair_members_dev.txt 2>&1
# The validation read (2_026_093_032, 64 requests): projection 289,804 ms, deadline 363,000 ms.
RAYON_NUM_THREADS=12 timeout 363 $bin executed evaluate order2 2026093032 64 $out/validation_order2_sections.txt \
  keys-founded=$keys/state_keys_founded.txt keys-lossless=$keys/state_keys_lossless.txt lossless opening \
  > $out/validation_order2_log.txt 2>&1
