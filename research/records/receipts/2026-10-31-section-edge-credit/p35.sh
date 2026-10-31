#!/usr/bin/env bash
# Record §35, acceptance 61 at the card, one lock: the race declaration's parity with participation
# at the clocked levels (heading-credited-every-level-participating), 24 streams over 32 sections,
# on bytes and on the founded units; then the card suite. Projection: the every-level parity ran
# 28.5 s (bytes) and 41 s (the wide alphabet's path); participation at two of six levels at most
# doubles the host's part: 90 s each; deadlines 300 s each, the suite's 300 s.
set -u
P=$ROOT/.local/wt/race/.local/race/passage
R=$ROOT/.local/wt/section-edge/.local/run
D=$R/race/units
BIN=${BIN:-$R/bin/tower_pass-35d}
E=$R/race/p35; mkdir -p $E
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
echo "BIN=$(sha256sum $BIN | cut -c1-64) NVIDIA_SMI $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,temperature.gpu,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
U=$ROOT/.local/wt/section-edge/research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY_receipts/UNITS
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity-bytes timeout 300 $BIN parity \
  $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level-participating > $E/parity-bytes.log 2>&1
echo "PARITY_BYTES rc=$? $(grep -E 'TOWER_PARTICIPATION|TOWER_PARITY_DONE|MEASURE|rror' $E/parity-bytes.log | tr '\n' ' ')"
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
  python3 -I $R/measure.py parity-units timeout 300 $BIN parity-units-founded \
  $U d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a \
  $D/TRAIN.bytes 60eb9909f38bc97882f57bf6c49c41d3550ba7ac47543bb28d3ee39ccd9265c0 \
  $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
  64 128 256 6 24 128 32 7 8 2 4 heading-credited-every-level-participating > $E/parity-units.log 2>&1
echo "PARITY_UNITS rc=$? $(grep -E 'TOWER_PARTICIPATION|TOWER_PARITY_DONE|MEASURE|rror' $E/parity-units.log | tr '\n' ' ')"
cd $ROOT/.local/wt/section-edge
PATH=/opt/cuda/bin:$PATH python3 -I $R/measure.py suite timeout 300 cargo test -p holonics-cuda --test tower_pass -- --include-ignored --test-threads=1 > $E/suite.log 2>&1
echo "SUITE rc=$? $(grep -E 'test result|FAILED|MEASURE' $E/suite.log | tr '\n' ' ')"
