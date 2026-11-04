#!/bin/bash
# §16.38's reads of conservation of faces (a still head's source shares its face's mass with its resonance class's definite
# sources, its score lowered by the octave of their count): (1) the sampled card parity (law27's read, 3 sections, 8 withheld
# problems, one write; 300 s measured, deadline 400 s); (2) the near copy lab, 130 laps (base: onset about lap 65, toy35
# onset.out); (3) the far copy lab, 100 laps (base: no copy in 100); (4) GSM8K, five fresh laps (base: the k4 read, 3.417,
# 3.149, 3.123, 3.003, 2.967). Projection: near 1.46 s a lap, 190 s, outer 470 s; far 8.45 s a lap, 845 s, lap bound 40 s,
# STOP_MS 1,000,000, outer 1,050 s; GSM8K 113 s a lap with its reads 125 s, 625 s, lap bound 160 s, STOP_MS 840,000, outer
# 880 s. The whole under 50 minutes once the card is free (it waits for the plateau read, which waits for run38).
# RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=${HOLONICS_ROOT:?the main checkout}; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; O=$W/.local/run/2026-11-03-faces38; BIN=$O/field_pass; Y=$W/.local/run/toy35
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
timeout 9000 bash -c "until [ \$(grep -c ': laps' $Y/plateau.out 2>/dev/null) -ge 7 ] || grep -qE 'LOCK_BUSY|never ended' $Y/plateau.out 2>/dev/null; do sleep 30; done" || { echo "FACES plateau never ended"; exit 75; }
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
toy near 30000 450000 470 130
toy far 40000 1000000 1050 100
rm -rf $O/gsm8k
$M gsm8k timeout 880 $BIN train complete-language train-field $TG 32 4 8 2 32 4 16 5 8 160000 160000 840000 $O/gsm8k > $O/gsm8k.log 2>&1
grep -E '^FIELD_JOINT ' $O/gsm8k.log | sed -E 's/.*lap=([0-9-]+) .*own_bits_a_byte=([0-9.]+) .*information_bits_a_byte=([0-9.-]+).*/  gsm8k lap \1 joint \2 information \3/'
grep -E '^FIELD_LAP ' $O/gsm8k.log | sed -E 's/.*lap=([0-9]+) .* ms=([0-9]+).*/  lap \1 ms \2/' | tr '\n' ' '; echo
echo "FACES exit"
