#!/usr/bin/env bash
# Record §23: where the credited heading's time goes, C′ and the credited heading profiled over 64 sections.
# The heading (uncredited) and the credited heading over the passage's first 64 sections, back to
# back on the idle card under one lock, from C′'s founding, no profile. Deadline 60 s each (the
# heading's 64 sections ran 25.1 s unprofiled at a38c1c63f, §18).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
BIN=${BIN:?the race binary}
R=$ROOT/.local/wt/section-edge/.local/run
E=$R/race/${PROF:?}; mkdir -p $E
echo "BIN=$(sha256sum $BIN | cut -c1-64)"
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING
export TOWER_PROFILE=1
export TOWER_LAP_SECTIONS=64
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
for run in "clocked:train-two-ladder-stacked-news-heading-credited-tower-classes" "every:train-two-ladder-stacked-news-heading-credited-every-level-tower-classes"; do
  IFS=: read -r name route <<< "$run"; O=$E/$name; mkdir -p $O
  echo "NVIDIA_SMI before $name: $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,clocks.mem,temperature.gpu,power.draw,pstate --format=csv,noheader) apps=$(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l) at=$(date -u +%FT%TZ)"
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py $name timeout 60 $BIN train complete-language $route 257 \
    $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
    $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
    $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 320 128 1 7 $O/lap0 > $O/lap0.log 2>&1
  echo "RUN_END $name rc=$? $(grep -E 'TOWER_SECTION.*section=64 ' $O/lap0.log) $(grep MEASURE $O/lap0.log)"
done
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
