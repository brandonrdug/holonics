"""A host ruler for the record of November 27 on the price of a shared label (the tensor-spectrum paper of November 24).

It reads five statements the record uses, each on a planted case, and prints one line a statement:
  1. the mean width W(S) = sqrt(2 pi) E max_s <g, s> of a 3-4-5 triangle against its half perimeter, 6;
  2. a segment with places inside it has the width of its two ends (the inside is free);
  3. the square of section 1.1: the geometric mean of two cut ranks is no price, since it does not add on a direct sum;
  4. on coprime rings, the lags at which two places sit nearest: the multiples of the rings' periods, never the short lags;
  5. the bound on holding m splits at once as one sum: the costliest split's price + W log2 m (the paper's (2.3)).
Floats are a ruler's here, never machinery. Seeded, so its lines are the same on every run.

  python3 -I width_ruler.py
"""
import math

import numpy as np

rng = np.random.default_rng(20261127)


def mean_width(points, draws=400_000, g=None):
    pts = np.asarray(points, dtype=np.float64)
    if g is None:
        g = rng.standard_normal((draws, pts.shape[1]))
    return math.sqrt(2 * math.pi) * float(np.mean(np.max(g @ pts.T, axis=1)))


tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]
print(f"1. triangle 3-4-5: W = {mean_width(tri):.3f}, half perimeter 6, three separate edge bits 12")

seg_ends = [(0.0,), (8.0,)]
seg_full = [(float(x),) for x in range(9)]
g1 = rng.standard_normal((400_000, 1))  # one set of draws for both, so the two lines differ only by the places inside
print(f"2. segment 0..8: W(ends) = {mean_width(seg_ends, g=g1):.3f}, W(ends and 7 places inside) = {mean_width(seg_full, g=g1):.3f}")

# Square corners split by its two midlines. U a horizontal wire, V a vertical one; ranks across (vertical cut, horizontal cut).
u, v = (2, 1), (1, 2)
gm = lambda r: math.sqrt(r[0] * r[1])
uv = (u[0] + v[0], u[1] + v[1])  # a direct sum adds ranks cut by cut
print(f"3. square: geometric mean of cut ranks U {gm(u):.4f}, V {gm(v):.4f}, U+V {gm(uv):.4f} against additive {gm(u) + gm(v):.4f}")

periods = (5, 7, 9)  # pairwise coprime; product 315


def ring_distance(lag):
    # place t on ring p at radius p/(2 pi), so one place is one unit of arc; chord at lag L is (p/pi)|sin(pi L/p)|
    return math.sqrt(sum((p / math.pi * math.sin(math.pi * lag / p)) ** 2 for p in periods) / len(periods))


lags = sorted(range(1, 316), key=ring_distance)[:6]
print("4. rings 5, 7, 9: nearest lags " + ", ".join(f"{L} ({ring_distance(L):.3f})" for L in lags)
      + f"; lag 1 {ring_distance(1):.3f}, lag 2 {ring_distance(2):.3f}")

span = 8.0
for m in (2, 3, 4, 8):
    print(f"5. span {span:g}, {m} splits held as one sum: at most the costliest split + {span * math.log2(m):.2f} bits")
