#!/bin/bash
# (The development read ran as `copy-field`; the command is `restate-field` since, its reads unchanged and two writer states added.)
# The near field by offset (§16.42). First the card's parity with the host on law27's sampled read (3 sections, 8 withheld
# problems, one write of 8 sweeps; D 32, H 4, n 8, still 2, f 32, K 2, paces drawn), now with each section's near field read
# on both (near_equal); then a development read of copy-field on main52 seg1's last state (STATE.10, 1.012 nats a place,
# D 256, H 4, K 4) over the first 8 held problems, each copy's first place, last place and the place after it, each alone
# open. Projection: the parity read 274 s (lane44's alone read, 273.7 s), deadline 400 s; the development read unmeasured,
# planned at one to three minutes, deadline 300 s. RTX 4080 SUPER under .local/gpu.lock (taken between main52's segment
# and its write, or its write and the next segment), 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-04-copy53; BIN=$O/field_pass; S=$W/.local/run/2026-11-04-main52/seg1
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "COPY LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) lock taken $(date -u +%H:%M:%S)"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
FIELD_PARITY_PACE=8 $M parity timeout 400 $BIN parity complete-language parity-field $T 32 4 8 2 32 2 16 3 8 1 1 8 8 > $O/parity.log 2>&1
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY_WRITES|FIELD_PARITY section|MEASURE|refused|rror|panic' $O/parity.log | sed -E 's/ (rows|reads|faces_unequal|covector_unequal|first|deposited|halvings|next|pace_nonzero|kappa)=[^ ]*//g' | cut -c1-260
rm -rf $O/dev
$M dev timeout 300 $BIN train complete-language copy-field $S/STATE.10 $(sha $S/STATE.10) $S/CODEC $(sha $S/CODEC) $G/UNITS0 $(sha $G/UNITS0) $G/HELD128.txt $(sha $G/HELD128.txt) 8 $O/dev > $O/dev.log 2>&1
grep -E '^FIELD_COPY|^FIELD_CARD |MEASURE|rror|panic' $O/dev.log | cut -c1-260
echo "COPY exit $(date -u +%H:%M:%S)"
