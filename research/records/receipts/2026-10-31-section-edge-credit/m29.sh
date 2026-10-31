#!/usr/bin/env bash
# Record §29 at the card, one lock: (1) the card's motive parity test and the card suite (debug
# build, deadlines 600 s and 300 s: the suite ran 17.9 to 29.3 s, the motive's three locksteps
# carry the series' terms); (2) the race declaration's parity, 24 streams over 32 sections,
# heading-credited-every-level-motive (deadline 300 s; the every-level parity ran 28.5 s);
# (3) the development read: the every-level credit's and the motive's first 64 sections from C′'s
# founding, alternated (deadline 180 s each: an unmeasured run is read for at most three minutes;
# the every-level read reached section 64 at 20.2 s).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
W=$ROOT/.local/wt/section-edge
R=$W/.local/run
BIN=$R/bin/tower_pass-29m
E=$R/race/m29; mkdir -p $E
echo "BIN=$(sha256sum $BIN | cut -c1-64) HEAD=$(git -C $W rev-parse --short HEAD) at=$(date -u +%FT%TZ)"
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
echo "LOCK_TAKEN at=$(date -u +%FT%TZ) $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader)"
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_LAP_SECTIONS TOWER_PROFILE TOWER_REFUSAL_CLOSURE
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
cd $W
python3 -I $R/measure.py motive-test timeout 600 cargo test -p holonics-cuda --test tower_pass the_cards_motive_is_the_hosts -- --include-ignored --test-threads=1 > $E/motive-test.log 2>&1
echo "MOTIVE_TEST rc=$? $(grep -E 'test result|MEASURE' $E/motive-test.log | tr '\n' ' ')"
grep -q 'test result: ok' $E/motive-test.log || { kill $VRAM; echo "STOP motive test failed"; exit 1; }
python3 -I $R/measure.py suite timeout 300 cargo test -p holonics-cuda -- --include-ignored --test-threads=1 > $E/suite.log 2>&1
echo "SUITE rc=$? $(grep -E 'test result|MEASURE' $E/suite.log | tr '\n' ' ')"
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity timeout 300 $BIN parity \
  $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level-motive > $E/parity.log 2>&1
echo "PARITY rc=$? $(grep -E 'TOWER_PARITY_DONE|MEASURE|rror' $E/parity.log | tr '\n' ' ')"
export TOWER_LAP_SECTIONS=64
for run in every:train-two-ladder-stacked-news-heading-credited-every-level-tower-classes motive:train-two-ladder-stacked-news-heading-credited-every-level-motive-tower-classes; do
  name=${run%%:*}; route=${run#*:}; O=$E/dev-$name; mkdir -p $O
  echo "NVIDIA_SMI before $name: $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,clocks.mem,temperature.gpu,power.draw,pstate --format=csv,noheader) at=$(date -u +%FT%TZ)"
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py dev-$name timeout 180 $BIN train complete-language $route 257 \
    $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
    $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
    $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 320 128 1 7 $O/lap0 > $O/lap0.log 2>&1
  echo "RUN_END $name rc=$? $(grep -E 'TOWER_SECTION.*section=(32|64) ' $O/lap0.log | tr '\n' ' ') $(grep -E 'TOWER_SERIES|TOWER_PASS |TOWER_CARD|MEASURE' $O/lap0.log | tr '\n' ' ')"
done
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
