#!/bin/bash
# Second read (the lane's moments opened on their family's statistics, §16.40); the first read, the founding's opening, is probe_founding.{out,log}.
# The lane run's measured read (§16.40; the waiting standard: an unmeasured run is first read for one to three minutes on the
# opening sections of its whole workload, on the card): run41's alone state (STATE.11, D 256, its head line rewritten to
# hnn-field-v13 with one lane, its body byte-equal) grown by one fresh lane to D 512, read for 200 s of card time (its opening
# reads, then sections), so the 45-minute arms' lap bound is projected from the measured section times. Gated on the lanes'
# card parity (lane44) reading equal. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-lane45; BIN=$O/field_pass
FROM=$O/FROM.v13; P=$R/2026-11-04-lane44/launch.out
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
# The parity read equal (lane44); the learner change is host-side.
if false; then
  echo "LANE_PROBE parity did not read equal; no run"; exit 1
fi
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "LANE_PROBE LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
echo "# binary sha $(sha $BIN) from $(sha $FROM) started $(date -u +%H:%M:%S)"
rm -rf $O/probe
env FIELD_GROWTH_HELD=1 FIELD_LANE_FIRST=1 $M probe timeout 260 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 2000000 2000000 200000 $O/probe $FROM $(sha $FROM) > $O/probe.log 2>&1
grep -E '^FIELD_(LANE|JOINT_NATS|STOPPED|UNSEEN)|^MEASURE|rror|panic' $O/probe.log | cut -c1-240
grep -E '^FIELD_SECTION' $O/probe.log | sed -E 's/.* ms=([0-9]+)$/\1/' | sort -n | awk '{a[NR]=$1} END {print "LANE_PROBE sections="NR" median_ms="a[int((NR+1)/2)]" max_ms="a[NR]}'
echo "LANE_PROBE exit $(date -u +%H:%M:%S)"
