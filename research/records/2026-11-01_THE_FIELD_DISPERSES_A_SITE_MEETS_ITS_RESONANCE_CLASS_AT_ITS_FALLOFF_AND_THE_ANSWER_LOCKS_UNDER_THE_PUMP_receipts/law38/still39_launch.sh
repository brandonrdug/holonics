#!/bin/bash
# §16.38's second read: conservation of faces with the still heads read at any distance (no falloff of distance on a still
# head; a turned head keeps it). (1) the sampled card parity (law27's read; 300 s, deadline 400 s); (2) the far copy lab,
# 100 laps (conservation of faces alone formed none in 84); (3) the near copy lab, 130 laps; (4) GSM8K, five fresh laps
# (conservation of faces alone: 3.410, 3.141, 3.100, 2.986, 2.950). Projection: far 11.9 s a lap (faces38), 100 laps 1,190 s,
# lap bound 40 s, STOP_MS 1,300,000, outer 1,350 s; near 1.5 s a lap, outer 470 s; GSM8K 125 s a lap with its reads, 625 s,
# lap bound 160 s, STOP_MS 840,000, outer 880 s. The whole under 55 minutes. RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-03-still39; BIN=$O/field_pass; Y=$W/.local/run/toy35
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
: # the card is free
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "FACES LOCK_BUSY"; exit 75; }
TG="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
echo "# binary sha $(sha $BIN)"
FIELD_PARITY_PACE=8 $M parity timeout 400 $BIN parity complete-language parity-field $TG 32 4 8 2 32 2 16 3 8 1 1 8 8 > $O/parity.log 2>&1
grep -E 'FIELD_PARITY_DONE|FIELD_PARITY_WRITE |MEASURE' $O/parity.log
toy() { # NAME LAP STOP OUTER LAPS
  local T="$G/UNITS0 $(sha $G/UNITS0) $Y/$1/TRAIN.txt $(sha $Y/$1/TRAIN.txt) $Y/$1/HELD.txt $(sha $Y/$1/HELD.txt) $K $(sha $K)"
  rm -rf $O/t_$1
  timeout $4 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 $5 8 $2 $2 $3 $O/t_$1 > $O/t_$1.log 2>&1
  python3 -I - $O/t_$1.log "$1" <<'EOF'
import sys, re
onset = below = last = None; laps = 0; rows = []
for l in open(sys.argv[1]):
    m = re.match(r'FIELD_JOINT lap=(\d+) .*own_bits_a_byte=([\d.]+) .*information_bits_a_byte=([-\d.]+)', l)
    if m:
        lap, own, inf = int(m[1]), float(m[2]), float(m[3]); laps = lap + 1; last = own
        if onset is None and inf > 0.1: onset = lap
        if below is None and own < 1.0: below = lap
        if lap % 10 == 9: rows.append(f"{lap}:{own:.3f}/{inf:.3f}")
print(f"{sys.argv[2]}: laps {laps} onset {onset} joint_below_1 {below} joint_last {last} | " + " ".join(rows), flush=True)
EOF
}
toy far 40000 1300000 1350 100
toy near 30000 450000 470 130
rm -rf $O/gsm8k
$M gsm8k timeout 880 $BIN train complete-language train-field $TG 32 4 8 2 32 4 16 5 8 160000 160000 840000 $O/gsm8k > $O/gsm8k.log 2>&1
grep -E '^FIELD_JOINT ' $O/gsm8k.log | sed -E 's/.*lap=([0-9-]+) .*own_bits_a_byte=([0-9.]+) .*information_bits_a_byte=([0-9.-]+).*/  gsm8k lap \1 joint \2 information \3/'
grep -E '^FIELD_LAP ' $O/gsm8k.log | sed -E 's/.*lap=([0-9]+) .* ms=([0-9]+).*/  lap \1 ms \2/' | tr '\n' ' '; echo
echo "FACES exit"
