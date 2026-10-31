#!/usr/bin/env bash
# Record §25: C′ (two laps), the clocked credit and the every-level credit (one lap each) on the
# register-capped forward, back to back in one session, each deadline fixed before its launch
# from its own 64-section read (x 726/64 x 1.2 a lap, 10 s a lap more), under one lock, from
# C′'s founding, no profile. VRAM sampled every 500 ms (cap 12 GB).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
BIN=${BIN:?the race binary}
R=$ROOT/.local/wt/section-edge/.local/run
E=$R/race/r25; mkdir -p $E
echo "BIN=$(sha256sum $BIN | cut -c1-64)"
exec 9>$ROOT/.local/gpu.lock
flock -w 60 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_LAP_SECTIONS TOWER_PROFILE TOWER_REFUSAL_CLOSURE
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
run() { local name=$1 route=$2 passes=$3 dl=$4; local O=$E/$name; mkdir -p $O
  echo "NVIDIA_SMI before $name: $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,clocks.mem,temperature.gpu,power.draw,pstate,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py $name timeout $dl $BIN train complete-language $route 257 \
    $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
    $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
    $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 320 128 $passes 7 $O/lap0 > $O/lap0.log 2>&1
  echo "RUN_END $name passes=$passes deadline_s=$dl rc=$? $(grep -E 'TOWER_SECTION.*section=64 ' $O/lap0.log | head -1) $(grep MEASURE $O/lap0.log)"; }
dl() { local t=$(grep -oE 'TOWER_SECTION pass=0 section=64 .*elapsed_ms=[0-9]+' $E/$1/lap0.log | grep -oE 'elapsed_ms=[0-9]+' | cut -d= -f2); [ -n "$t" ] || { echo "DEV_READ_FAILED $1"; kill $VRAM; exit 6; }; echo $(( t * 726 * 12 * $2 / 640 / 1000 + 10 * $2 )); }
for r in cprime:train-two-ladder-stacked-news-packet-tower-classes clocked:train-two-ladder-stacked-news-heading-credited-tower-classes every:train-two-ladder-stacked-news-heading-credited-every-level-tower-classes; do
  TOWER_LAP_SECTIONS=64 run dev-${r%%:*} ${r#*:} 1 60
done
DC=$(dl dev-cprime 2); DK=$(dl dev-clocked 1); DE=$(dl dev-every 1)
echo "PROJECTION cprime two laps ${DC} s, clocked one lap ${DK} s, every one lap ${DE} s"
run cprime train-two-ladder-stacked-news-packet-tower-classes 2 $DC
run clocked train-two-ladder-stacked-news-heading-credited-tower-classes 1 $DK
run every train-two-ladder-stacked-news-heading-credited-every-level-tower-classes 1 $DE
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
