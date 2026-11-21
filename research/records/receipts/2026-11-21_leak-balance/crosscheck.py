"""The two receipts of the built tick read against each other (host arithmetic on committed figures).

chart_step_ratio_milli of receipts/2026-11-20_engineering/tick_residual_L71.txt: the energy ratio of successive chart
steps, pooled over the region. On x <- x + g(r(x)) about a fixed ray, a mode of exponent nu at fill F has
  chart deviation ratio (F + nu)/(F + 1), chart step ratio (F + nu)/(F + 2),
so 1/(1 - r_k) = (F_(k-1) + 2)/(2 - nu) is a line in k of slope 1/(2 - nu).
"""
import math
ratio_milli = {1: 784, 2: 674, 3: 153, 4: 110, 5: 235, 6: 361, 7: 452, 8: 522, 9: 576, 10: 620}
step_over_state_micro = [5923141, 538678, 1507531, 2416223, 442739, 157061, 79591, 47976, 32073, 22963, 17248, 13442]
ks = [5, 6, 7, 8, 9, 10]
ys = [1.0 / (1.0 - math.sqrt(ratio_milli[k] / 1000.0)) for k in ks]
n = len(ks); mx = sum(ks) / n; my = sum(ys) / n
slope = sum((k - mx) * (y - my) for k, y in zip(ks, ys)) / sum((k - mx) ** 2 for k in ks)
icpt = my - slope * mx
nu = 2.0 - 1.0 / slope
# 1/(1-r_k) = (k - 1 + a + 2)/(2 - nu)  =>  a = icpt*(2 - nu) - 1
a = icpt * (2.0 - nu) - 1.0
print(f"CROSS line 1/(1-r_k) k=5..10: " + " ".join(f"{y:.4f}" for y in ys))
print(f"CROSS slope={slope:.4f} nu={nu:.3f} a={a:.2f}")
for k in range(4, 11):
    F = k - 1 + a
    pred = ((F + nu) / (F + 2)) ** 2
    print(f"CROSS k={k} chart_step_energy_ratio predicted={pred:.3f} measured={ratio_milli[k]/1000:.3f}")
fills = [1.0 / math.sqrt(v / 1e6) for v in step_over_state_micro]
print("CROSS fill_k=state/step k=0..11: " + " ".join(f"{f:.2f}" for f in fills))
print("CROSS fill_k - k, k=5..11: " + " ".join(f"{fills[k]-k:.2f}" for k in range(5, 12)))
chart_step = [1413521, 1108363, 747040, 114342, 12656, 2979, 1077, 488, 255, 147, 91]
print("CROSS chart step (degrees of chord) k=0..10: " + " ".join(f"{math.degrees(2*math.asin(min(1,math.sqrt(v/1e6)/2))):.1f}" for v in chart_step))
# what the three kinds are against the fill
for name, nu_j in (("released end", -0.54), ("held", 0.0), ("boosted end", 0.19)):
    print(f"KIND {name}: nu={nu_j:+.2f} chart exponent on the fill -(1-nu)={-(1-nu_j):+.2f}  multiplier under a leak delta: 1-{1-nu_j:.2f}*delta  (delta=1/2: {1-0.5*(1-nu_j):.3f}; delta=1: {nu_j:+.2f})")
emin, emax = 1 - 0.19, 1 + 0.54
d = 2 / (emin + emax); rho = (emax - emin) / (emax + emin)
print(f"REST delta*=2/(eps_min+eps_max)={d:.3f} quality Q*=1/delta*={1/d:.3f} radius={(rho):.3f} ticks_for_2^-12={math.log(2**-12)/math.log(rho):.1f} friction d*={d/(1-d):.2f}")
for dl in (0.25, 0.5, 0.75):
    r = max(abs(1 - dl * emin), abs(1 - dl * emax))
    print(f"REST delta={dl}: radius={r:.3f} ticks_for_2^-12={math.log(2**-12)/math.log(r):.1f}")
# built tick: ticks for the slow mode's chart deviation to fall 2^-12 from tick 4: ((F+..)^-0.81)
F4 = 4 + a
print(f"BUILT ticks for the slow mode to fall 2^-12 from fill {F4:.2f}: {F4*(2**(12/0.81)) - F4:.0f}; to fall by half: {F4*(2**(1/0.81)) - F4:.1f}")
