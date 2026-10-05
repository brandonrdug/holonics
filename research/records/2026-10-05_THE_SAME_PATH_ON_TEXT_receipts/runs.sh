#!/usr/bin/env bash
# The text loop's runs (research/records/2026-10-05_THE_SAME_PATH_ON_TEXT_KEY_LOCATION_AND_THE_RELEASE_ON_THE_BYTE_CHART.md),
# each run once, from the worktree root, at the build of the record's commit. Thread budget 12.
# Every byte goes to the private directory .local/text_loop/ (never committed); the logs below carry
# counts only. HOLONICS_CUTS names the directory holding the private cuts (the main checkout's
# .local/cuts).
set -u
bin=./target/release/examples/hnn_prediction
out=research/records/2026-10-05_THE_SAME_PATH_ON_TEXT_receipts
cut=${HOLONICS_CUTS:-.local/cuts}/curated-u6-choosing-flat-cut.bin
# Development (timing): the window after the training passage, on every state; first read, deadline 600 s.
RAYON_NUM_THREADS=12 timeout 600 $bin executed text "$cut" .local/text_loop/dev dev > $out/dev_log.txt 2>&1
# The pinned run: the 16 requests (projection 867,840 ms, deadline 1,085 s; the record's §0).
RAYON_NUM_THREADS=12 timeout 1085 $bin executed text "$cut" .local/text_loop/run run > $out/run_log.txt 2>&1
# The pinned run stopped early (the record's §0): the founded state alone, the requests one after
# another, its share of the pinned projection, launched with no other run on the cores.
RAYON_NUM_THREADS=12 timeout 961 $bin executed text "$cut" .local/text_loop/run run founded > $out/run_founded_log.txt 2>&1
# The triples, written to the private directory; stdout carries the copy lengths (integers).
python3 $out/triples.py .local/text_loop/run lossless founded > $out/copy_lengths.txt
