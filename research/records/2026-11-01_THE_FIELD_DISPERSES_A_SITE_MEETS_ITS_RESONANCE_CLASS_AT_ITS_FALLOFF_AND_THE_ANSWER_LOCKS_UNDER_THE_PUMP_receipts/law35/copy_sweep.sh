#!/bin/bash
# §16.35's copy read: is the field's attention able to cohere an answer with its question? Two terrains whose answer copies
# its question's eight letters in order (make_copy_toy.py): near (the letters end the question line, about 10 places back)
# and far (288 dots between, about 300 places back, GSM8K's median 306). Today's declaration (D 32, H 4, n 8, still 2, f 32,
# K 4, section 16, rate 8), 20 laps from a fresh founding each. The joint read's information (own question against the next
# problem's) is the copy's: at most about 2.1 bits a byte (8 letters at 3 to 4 bits and the last line's letter, of 15 answer
# bytes and the void). Projection: near regions are about 30 sites (a lap about 2 s), far about 320 (a lap about 15 s from
# GSM8K's 0.27 s a section of about 600 sites, 125 sections); lap bounds 30 s and 40 s, STOP_MS 240,000 and 600,000, outer
# 260 s and 640 s; the two under 15 minutes. RTX 4080 SUPER under .local/gpu.lock (waits for run36 and void35), 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy35; BIN=$W/.local/run/2026-11-03-void35/field_pass_close
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "SWEEP LOCK_BUSY"; exit 75; }
run() {
  local name=$1 lap=$2 stop=$3 outer=$4; shift 4
  local T="$G/UNITS0 $(sha $G/UNITS0) $O/$name/TRAIN.txt $(sha $O/$name/TRAIN.txt) $O/$name/HELD.txt $(sha $O/$name/HELD.txt) $K $(sha $K)"
  rm -rf $O/s_$name
  timeout $outer $BIN train complete-language train-field $T "$@" $lap $lap $stop $O/s_$name > $O/s_$name.log 2>&1
  echo "$name: laps $(grep -c '^FIELD_LAP ' $O/s_$name.log) lap_ms $(grep -E '^FIELD_LAP ' $O/s_$name.log | tail -1 | sed -E 's/.* ms=([0-9]+).*/\1/') grow $(grep -c '^FIELD_GROW ' $O/s_$name.log)"
  grep -E '^FIELD_JOINT lap=(0|1|2|4|9|14|19) ' $O/s_$name.log | sed -E 's/.*lap=([0-9-]+) .*own_bits_a_byte=([0-9.]+) foil_bits_a_byte=([0-9.]+) information_bits_a_byte=([0-9.-]+).*/  lap \1 own \2 foil \3 information \4/'
}
run near 30000 240000 260 32 4 8 2 32 4 16 20 8
run far 40000 600000 640 32 4 8 2 32 4 16 20 8
