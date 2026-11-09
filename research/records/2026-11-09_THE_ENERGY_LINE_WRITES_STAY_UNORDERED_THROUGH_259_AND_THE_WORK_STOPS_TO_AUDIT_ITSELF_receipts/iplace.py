#!/usr/bin/env python3
"""Per held place, the order difference of the split 239 -> 249 (theory, November 9 14:17): I = theta's move at 239's maps less its
move at 249's, G'(t249; C239) - G'(t239; C239) - G'(t249; C249) + G'(t239; C249), classes held; G' is G less beta at each theta.
Args: PLAIN239(enum:lap) PLAIN249(enum:lap) UNDER_239_249 UNDER_249_239 STATE239 STATE249 OUT. A reading only."""
import sys
sys.argv = sys.argv  # split3's helpers
exec(open(__file__.replace('iplace.py', 'split3.py')).read().split('pb,ps,ubh,ub,sb,ss=')[0])
p239, p249, u_a, u_b, s239, s249, out = sys.argv[1:8]
B239, B249 = betas(theta(s239)), betas(theta(s249))
G239 = codes(p239, B239); G249 = codes(p249, B249)
Ga = codes(u_a, B249)   # theta 249 under 239's classes
Gb = codes(u_b, B239)   # theta 239 under 249's classes
ks = [k for k in G239 if k in G249 and k in Ga and k in Gb]
I = {k: (Ga[k] - G239[k]) - (G249[k] - Gb[k]) for k in ks}
tot = sum(v * v for v in I.values())
print(f"places {len(ks)}: sum I^2 {tot:.1f}, RMS {(tot / len(ks)) ** 0.5:.3f}, mean {sum(I.values()) / len(ks):+.4f}")
with open(out, "w") as f:
    f.write("problem\tplace\tI\n")
    for k in ks:
        f.write(f"{k[0]}\t{k[1]}\t{I[k]:.6f}\n")
