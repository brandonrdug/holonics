#!/usr/bin/env bash
# Record §32: each period (digits, sentence) one pass of 64 sections of 128 on one stream from C′'s
# founding with every level's credit, each section read, then one pass continued from its saved
# state. Deadline 120 s each (a section on one stream reads in tens of milliseconds; the founding and
# the held-out read some seconds).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/period
BIN=$R/bin/tower_pass-32a
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_LAP_SECTIONS TOWER_PROFILE TOWER_REFUSAL_CLOSURE
export TOWER_WINDOW_SECTIONS=1
echo "BIN=$(sha256sum $BIN | cut -c1-64) at=$(date -u +%FT%TZ)"
for name in digits sentence; do
  T=$D/$name.TRAIN.classes; V=$D/$name.DEV.classes; O=$D/$name.DEV.roles
  for run in pass:"" cont:from; do
    tag=${run%%:*}; out=$D/$name-$tag; rm -rf $out
    extra=""; [ "$tag" = cont ] && extra="$D/$name-pass/STATE $(sha256sum $D/$name-pass/STATE | cut -c1-64)"
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
      python3 -I $R/measure.py $name-$tag timeout 120 $BIN train complete-language train-two-ladder-stacked-news-heading-credited-every-level-tower-classes 257 \
      $T $(sha256sum $T | cut -c1-64) $V $(sha256sum $V | cut -c1-64) $O $(sha256sum $O | cut -c1-64) \
      $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
      64 128 256 6 1 128 1 7 $out $extra > $out.log 2>&1
    echo "RUN_END $name-$tag rc=$? $(grep -E 'TOWER_PASS |MEASURE' $out.log | tr '\n' ' ')"
    grep TOWER_SECTION $out.log | grep -oE 'section=[0-9]+ bits_a_byte=[0-9.]+' | head -20 | tr '\n' ' '; echo
  done
done
