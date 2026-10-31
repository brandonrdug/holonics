#!/usr/bin/env bash
# C′ (the packeted race declaration) continued from its five-lap state (held-out 1.986) for 15 more passes,
# beside the every-level credit continued to 20 (1.852), on tower_pass-30a (C′'s kernels unchanged), held-out read each pass, then its releases (six
# prompts, 1,024 classes, agree 1) from each state whose summed elapsed time crosses an hour mark.
# Projection: 15 passes x 225.0 s (C′'s largest measured lap, §22) = 3,375 s;
# deadline 3,720 s (a tenth more). Releases 60 s deadline each (six prompts took 8-9 s).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
BIN=$R/bin/tower_pass-30a
FROM=$R/race/ext/cprime/lap0/STATE
E=$R/race/contc; mkdir -p $E
echo "BIN=$(sha256sum $BIN | cut -c1-64) FROM=$(sha256sum $FROM | cut -c1-64) at=$(date -u +%FT%TZ)"
exec 9>$ROOT/.local/gpu.lock
flock -w 600 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_LAP_SECTIONS TOWER_PROFILE TOWER_REFUSAL_CLOSURE
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
echo "NVIDIA_SMI before: $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,power.draw,memory.used --format=csv,noheader)"
O=$E/cprime; mkdir -p $O
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py cprime timeout 3720 $BIN train complete-language \
  train-two-ladder-stacked-news-packet-tower-classes 257 \
  $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
  $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
  $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 320 128 15 7 $O/lap0 $FROM $(sha256sum $FROM | cut -c1-64) > $O/lap0.log 2>&1
echo "RUN_END cprime rc=$? $(grep MEASURE $O/lap0.log)"
grep TOWER_PASS $O/lap0.log
# Releases at each hour mark of summed elapsed time (C′'s five laps 1,130,200 ms before this run, §22).
hour=3600000; prior=1130200
for k in $(seq 0 14); do
  ms=$(grep -E "^TOWER_PASS pass=$k " $O/lap0.log | grep -oE 'elapsed_ms=[0-9]+' | cut -d= -f2)
  [ -n "$ms" ] || break
  if [ $((prior + ms)) -ge $hour ] || [ $k -eq 14 ]; then
    S=$O/lap0/STATE.$k
    echo "RELEASE from STATE.$k summed_elapsed_ms=$((prior + ms))"
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
      python3 -I $R/measure.py release$k timeout 60 $BIN release complete-language release-tower-classes \
      $S $(sha256sum $S | cut -c1-64) $P/PROMPTS.classes b45cf44ee3a5dd6b84e4b76c23cbab77e1816b1a903b4e7d394c445f9b6b7e3b \
      $P/RELEASE_KEYS 9e358671eb6968c1f4b624611b41de7fed4ede5fc1af9532a8d9db36f3c9b739 1024 1 $O/release$k > $O/release$k.log 2>&1
    echo "RELEASE_END $k rc=$? $(grep MEASURE $O/release$k.log)"
    [ $((prior + ms)) -ge $hour ] && hour=$((hour + 3600000))
  fi
done
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
