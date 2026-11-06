#!/bin/bash
# The depth ring against its foil (the unified-theory readings of November 6, 04:34 to 04:52): code86's segment-3 state with head
# 3 made a depth ring (ring-field, r founded at zero; RING.0) and code86's state unconverted, each trained four laps under
# code86's own laws (the front cut path states, the per-blank clock, the near tail), the same seed and keys, two segments of two
# laps each, interleaved; after each segment both write the 32 held given keyed100's lengths (closing92's sweeps, runs, no refine
# pass). First the sampled parity under the ring (FIELD_DEPTH=1). Fixed: far brackets at least 0.8 of held's closure with near
# at least 0.9, openers left unclosed under 0.1 (keyed100: 0.42); held context against the foil's. If short: split by whether a
# pair's between-sites were resolved at its later end's draw, and run the conversion with r held at zero before reading the miss
# as the ring's. Projection: parity 336 s measured (deadline 900 s); a lap about 255 s (code86), its bound 304,236 ms (code86's
# cost read); a segment two laps plus 300 s (outer 970 s); each write 900 s. About 1 h. Detached; RTX 4080 SUPER under
# .local/gpu.lock (waited on up to 7,200 s), 24 host threads. It waits for code91.
set -u
export FIELD_PATH_FRONT_CUT=1 FIELD_CLOCK_PER_BLANK=1
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-06-ring102; BIN=$O/field_pass; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
T="$U0 $(sha $U0) $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K)"
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC; E=$R/2026-11-05-closing92/both_refine0/ENDS.tsv
lock() { exec 9>$ROOT/.local/gpu.lock; flock -w 7200 9 || { echo "MAIN LOCK_BUSY"; exit 75; }; }
echo "# ring102 waits for code91 $(date -u +%H:%M:%S)"
until grep -qE "^MAIN exit|chain stops|LOCK_BUSY" $R/2026-11-06-code91/launch.out; do sleep 20; done
lock
echo "# ring102 binary $(sha $BIN) parity lock taken $(date -u +%H:%M:%S)"
FIELD_DEPTH=1 FIELD_PARITY_PACE=8 $M parity timeout 900 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 1 8 1 1 8 8 > $O/parity.log 2>&1
exec 9>&-
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY section|MEASURE|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-300
grep -qE 'FIELD_PARITY_DONE .*reads_unequal=0 faces_unequal=0 covector_unequal=0 learners_unequal=0 .*releases_unequal=0' $O/parity.log || { echo "PARITY FAILED: the chain stops $(date -u +%H:%M:%S)"; exit 1; }
for f in faces_unequal=0 covector_unequal=0 learner_equal=true near_equal=true clocks_equal=true rows_equal=true shares_equal=true currents_equal=true; do
  grep -E 'FIELD_PARITY section' $O/parity.log | grep -qv "$f" && { echo "PARITY FAILED on $f: the chain stops"; exit 1; }
done
L=304236; SEG=$((2 * L + 300000)); OUTER=$((SEG / 1000 + 60))
segment() { # NAME FROM
  lock
  echo "# $1 from $(sha $2) started $(date -u +%H:%M:%S)"
  rm -rf $O/$1
  FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 $M $1 timeout $OUTER $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 $L $L $SEG $O/$1 $2 $(sha $2) > $O/$1.log 2>&1
  S=$(ls -t $O/$1/STATE.* 2>/dev/null | grep -v stopped | head -1)
  [ -n "$S" ] || { exec 9>&-; echo "$1 no state"; exit 1; }
  rm -rf $O/$1_write
  FIELD_WRITER_LENGTHS=$E FIELD_WRITER_RUN_BITS=1 $M $1_write timeout 900 $BIN train complete-language length-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 2062 0 3000000 $O/$1_write > $O/$1_write.log 2>&1
  exec 9>&-
  grep -E '^FIELD_(LAPS_HELD|STOPPED)|^FIELD_LAP |^MEASURE|rror|panic' $O/$1.log | sed -E 's/ sites=[0-9]+//' | cut -c1-200
  grep -E '^FIELD_HELD' $O/$1.log | sed -E 's/.*lap=(-?[0-9]+) answer=([0-9.-]+).*context=([0-9.]+).*foil=([0-9.]+).*/\1:\2:\3:\4/' | tr '\n' ' '; echo
  grep -E '^FIELD_SECTION' $O/$1.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1} END {printf "sections mean ms %.0f over %d\n", s/n, n}'
  echo "== $1 write given keyed100's lengths"
  grep -E '^FIELD_LENGTH|^MEASURE' $O/$1_write.log | cut -c1-200
  python3 -I $O/collapse.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv | head -1
  python3 -I $O/code_reading.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv | sed -n 2p
  python3 -I $O/code_closure.py $P/HELD128.txt $O/$1_write/SAMPLE.tsv
  echo "SEGMENT $1 done $(date -u +%H:%M:%S)"
}
segment ring1 $O/RING.0
segment foil1 $R/2026-11-05-code86/seg3/STATE.4
segment ring2 $(ls -t $O/ring1/STATE.* | grep -v stopped | head -1)
segment foil2 $(ls -t $O/foil1/STATE.* | grep -v stopped | head -1)
echo "MAIN exit $(date -u +%H:%M:%S)"
