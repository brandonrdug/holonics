#!/usr/bin/env bash
# Record §22, the race toward an hour: the credited heading three more laps from its first, then C′ three more from its second, back to back under
# one lock, from C′'s founding, no profile, no TOWER_LAP_SECTIONS, MemoryMax 8G. Deadlines from the
# development read (DL_C, DL_H, fixed before launch). VRAM sampled every 500 ms (cap 12 GB).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
BIN=${BIN:?the race binary}
R=$ROOT/.local/wt/section-edge/.local/run
E=$R/race/ext; mkdir -p $E; Q=$R/race/eq
echo "BIN=$(sha256sum $BIN | cut -c1-64)"
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_LAP_SECTIONS TOWER_PROFILE
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
for run in "credited:train-two-ladder-stacked-news-heading-credited-tower-classes:3:${DL_H:?}:$Q/credited/lap0/STATE.0:${H0:?}" "cprime:train-two-ladder-stacked-news-packet-tower-classes:3:${DL_C:?}:$Q/cprime/lap0/STATE.1:${C1:?}"; do
  IFS=: read -r name route passes dl from fromsha <<< "$run"; O=$E/$name; mkdir -p $O
  echo "NVIDIA_SMI before $name: $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,clocks.mem,temperature.gpu,power.draw,pstate,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py $name timeout $dl $BIN train complete-language $route 257 \
    $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
    $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
    $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 320 128 $passes 7 $O/lap0 $from $fromsha > $O/lap0.log 2>&1
  echo "RUN_END $name passes=$passes deadline_s=$dl rc=$? $(grep MEASURE $O/lap0.log)"
done
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
