#!/usr/bin/env bash
# Record §30's development read, read by parts: the motive's first 64 sections from C′'s
# founding under the declared parts reading (TOWER_REFUSAL_PARTS=1; it moves nothing), each refused
# step read again under each part alone (the descents D and D↓, the heading's read, the readout,
# the clocked levels' material, the rest). Projection: the development read's 46.3 s plus five
# forwards a refusal at its 76 ms a forward over its 205 refusals, 78 s: 125 s; deadline 160 s.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
BIN=${BIN:-$R/bin/tower_pass-30a}
E=$R/race/p30; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_HOLD TOWER_MEETING TOWER_PROFILE TOWER_REFUSAL_CLOSURE
export TOWER_LAP_SECTIONS=64 TOWER_REFUSAL_PARTS=1
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
O=$E/motive; mkdir -p $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parts timeout 160 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-motive-tower-classes 257 \
  $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
  $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
  $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 320 128 1 7 $O/lap0 > $O/lap0.log 2>&1
echo "RUN_END parts rc=$? $(grep -E 'TOWER_SECTION|TOWER_REFUSAL_PARTS pass|TOWER_REFUSALS|MEASURE' $O/lap0.log | tr '\n' ' ')"
