#!/usr/bin/env -S python3 -I
"""g86_part_octaves.py POLAR_MAP ...: each founded part's polarization and the octave G86's law gives it, from polar_map.py's printed
block lines (a host ruler on printed lines, never machinery; floats as a ruler). A part is the sum of the blocks it holds; pi_F is the
field's fall two laps on over its heat (every part at the floor on the rt line). The octave is the nearest to log2(pi/pi_F), held at
0 or above and 0 where pi <= 0. The added heat prices each part at 2^octave, the added fall at (2^octave)^0.944 (G84's exponent).
"""
import os, re, sys, math
from collections import defaultdict
# blocks -> parts, approximating each part by the polar map's blocks (a ruler on printed lines)
def load(path):
    b = {}
    for line in open(path):
        if not line.startswith("POLAR_BLOCK"): continue
        kv = dict(re.findall(r"(\w+)=([^\s]+)", line))
        b[(kv["block"], kv["lane"], kv["contacts"])] = (float(kv["heat_micro"]), float(kv["fall2_micro"]))
    return b
parts = {
 "w_new": [("w","1","new"),("w","2","new")],
 "a_new": [("a","1","new"),("a","2","new"),("a_bias","0","new")],
 "b_new": [("b","1","new"),("b","2","new"),("b_bias","0","new")],
 "enc_lane": [("enc","2","all")], "before_lane": [("before","2","all")], "after_lane": [("after","2","all")],
 "q_lane": [("q","2","all")], "v_lane": [("v","2","all")], "probe_lane": [("probe","2","all")],
 "out_lane": [("out","2","all")], "moment_face_lane": [("moment_face","2","all")],
 "face_biases_lane": [("w_bias","2","all"),("out_bias","2","all"),("moment_face_bias","2","all"),("lift_bias","2","all")],
 "a_lane": [("a","2","old")], "b_lane": [("b","2","old")],
 "enc_first": [("enc","1","all")], "before_first": [("before","1","all")], "after_first": [("after","1","all")],
}
for path in sys.argv[1:]:
    b = load(path)
    H = sum(h for h, f in b.values()); F = sum(f for h, f in b.values())
    piF = F / H
    print(f"# {os.path.basename(path)}: blocks {len(b)} heat {H:.1f} fall2 {F:+.1f} pi_F {piF:.4f}")
    dh = df = 0.0
    for name, keys in parts.items():
        missing = [k for k in keys if k not in b]
        h = sum(b[k][0] for k in keys if k in b); f = sum(b[k][1] for k in keys if k in b)
        pi = f / h if h else float("nan")
        x = math.log2(pi / piF) if pi > 0 else float("-inf")
        o = max(0, math.floor(x + 0.5)) if pi > 0 else 0
        o = min(o, 11)
        dh += h * (2**o - 1); df += f * ((2**o) ** 0.944 - 1)
        print(f"{name:18s} heat {h:8.1f} fall2 {f:+7.1f} pi {pi:+.3f} log2(pi/piF) {x:+.2f} octave {o}" + (f" missing {missing}" if missing else ""))
    print(f"# added heat {dh:.0f} ({dh/H:+.1%}), added fall2 at 0.944 {df:+.0f} ({df/F:+.1%})")
