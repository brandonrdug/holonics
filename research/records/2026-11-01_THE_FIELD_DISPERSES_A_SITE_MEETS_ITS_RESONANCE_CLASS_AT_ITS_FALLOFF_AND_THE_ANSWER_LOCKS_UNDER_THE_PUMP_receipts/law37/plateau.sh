#!/bin/bash
# §16.37's plateau read: what shortens the copy's plateau? The near copy terrain (make_copy_toy.py near), 130 laps each from a
# fresh founding: the base (onset.out: the question's information first above 0.1 at about lap 70, the joint below 1.0 by
# lap 99, 0.03 by lap 119) against one change each: the returns founded drawn (FIELD_FOUND_RETURNS=returns), the readout's
# lift drawn too (=lift), the rate 2^(-7), sections of 8, two ticks, every head still. Each row: the first lap whose
# information passes 0.1, the first lap whose joint falls below 1.0, the joint at lap 129. Projection: 1.46 s a lap
# (onset.out's near), 130 laps 190 s, a lap of sections of 8 or of two ticks at most twice that; lap bound 30 s, STOP_MS
# 450,000, outer 470 s a variant; the seven under 30 minutes once the card is free (the lock waits for run38).
# RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/toy35; BIN=$W/.local/run/2026-11-03-run38/field_pass
sha() { sha256sum "$1" | cut -c1-64; }
# Run38 first: wait for its exit line (at most two hours), then take the card.
timeout 7200 bash -c "until grep -qE 'FIELD_RUN exit|LOCK_BUSY|no state' $W/.local/run/2026-11-03-run38/launch.out 2>/dev/null; do sleep 30; done" || { echo "SWEEP run38 never ended"; exit 75; }
exec 9>$ROOT/.local/gpu.lock
flock -w 7200 9 || { echo "SWEEP LOCK_BUSY"; exit 75; }
T="$G/UNITS0 $(sha $G/UNITS0) $O/near/TRAIN.txt $(sha $O/near/TRAIN.txt) $O/near/HELD.txt $(sha $O/near/HELD.txt) $K $(sha $K)"
run() { # NAME ENV D H n STILL f K SECTION RATE
  local name=$1 env=$2; shift 2
  rm -rf $O/p_$name
  env $env timeout 470 $BIN train complete-language train-field $T $1 $2 $3 $4 $5 $6 $7 130 $8 30000 30000 450000 $O/p_$name > $O/p_$name.log 2>&1
  python3 -I - $O/p_$name.log "$name" <<'EOF'
import sys, re
onset = below = last = None; laps = 0
for l in open(sys.argv[1]):
    m = re.match(r'FIELD_JOINT lap=(\d+) .*own_bits_a_byte=([\d.]+) .*information_bits_a_byte=([-\d.]+)', l)
    if m:
        lap, own, inf = int(m[1]), float(m[2]), float(m[3]); laps = lap + 1; last = own
        if onset is None and inf > 0.1: onset = lap
        if below is None and own < 1.0: below = lap
print(f"{sys.argv[2]}: laps {laps} onset {onset} joint_below_1 {below} joint_last {last}", flush=True)
EOF
}
run base "FIELD_NONE=1" 32 4 8 2 32 4 16 8
run returns "FIELD_FOUND_RETURNS=returns" 32 4 8 2 32 4 16 8
run lift "FIELD_FOUND_RETURNS=lift" 32 4 8 2 32 4 16 8
run rate7 "FIELD_NONE=1" 32 4 8 2 32 4 16 7
run section8 "FIELD_NONE=1" 32 4 8 2 32 4 8 8
run ticks2 "FIELD_NONE=1" 32 4 8 2 32 2 16 8
run still4 "FIELD_NONE=1" 32 4 8 4 32 4 16 8
