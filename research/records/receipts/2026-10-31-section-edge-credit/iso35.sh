#!/usr/bin/env bash
# Record §35: the card's covector parted from the host's from section 4 beside the every-level
# credit; which partner carries it. Eight sections each (the section-4 departure inside them),
# 24 streams: the credited declaration again, the heading without the credit, the packets alone.
# Projection: the credited parity's 68.5 s over 32 sections, about 20 s each; deadline 120 s each.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
BIN=${BIN:-$R/bin/tower_pass-35c}
E=$R/race/p35; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
echo "BIN=$(sha256sum $BIN | cut -c1-64) at=$(date -u +%FT%TZ)"
for w in heading-credited-every-level-participating heading-participating packets-participating; do
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py iso-$w timeout 120 $BIN parity \
    $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
    $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 24 128 8 7 8 2 4 $w > $E/iso-$w.log 2>&1
  echo "ISO $w rc=$? $(grep -E 'TOWER_PARITY_FIRST|TOWER_PARITY_DONE|MEASURE|rror' $E/iso-$w.log | head -3 | tr '\n' ' ')"
done
