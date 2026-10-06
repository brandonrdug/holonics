#!/usr/bin/env python3
"""[measured-diagnostic; exact] The anchor Fisher form F = sum z z^T read exactly from the samples: tr F, the reading where the
accumulated energy first reaches 1, and the cell [k, k+1)/2^24 holding the largest eigenvalue,
located by exact LDL^T pivots of cI - F (all positive iff c > lambda_max)."""
import sys
from fractions import Fraction


def read(path):
    zs = []
    for line in open(path):
        parts = line.split()
        if not parts or parts[0] != "sample" or "|" not in parts:
            continue
        cut = parts.index("|")
        zs.append([Fraction(x) for x in parts[3:cut]])
    return zs


def positive_definite(a):
    n = len(a)
    a = [row[:] for row in a]
    for k in range(n):
        if a[k][k] <= 0:
            return False
        for i in range(k + 1, n):
            f = a[i][k] / a[k][k]
            if f:
                for j in range(k + 1, n):
                    a[i][j] -= f * a[k][j]
    return True


zs = read(sys.argv[1])
n = len(zs[0])
F = [[Fraction(0)] * n for _ in range(n)]
total, reach = Fraction(0), None
for t, z in enumerate(zs, 1):
    for i in range(n):
        if z[i]:
            for j in range(n):
                F[i][j] += z[i] * z[j]
    total += sum(x * x for x in z)
    if reach is None and total >= 1:
        reach = t
trace = sum(F[i][i] for i in range(n))
grid = 2 ** 24
print(f"readings {len(zs)}, width {n}")
print(f"tr F = {trace.numerator}/{trace.denominator}, in [{trace * grid // 1}/2^24, {trace * grid // 1 + 1}/2^24)")
print(f"accumulated energy first reaches 1 at reading {reach}")
def pd(c):
    return positive_definite([[(c if i == j else 0) - F[i][j] for j in range(n)] for i in range(n)])
lo, hi = 0, int(trace * grid) + 1  # lambda_max <= tr F
assert pd(Fraction(hi, grid)) and not pd(Fraction(lo, grid))
while hi - lo > 1:
    mid = (lo + hi) // 2
    if pd(Fraction(mid, grid)):
        hi = mid
    else:
        lo = mid
print(f"largest eigenvalue of F in [{lo}/2^24, {hi}/2^24): {hi}/2^24 I - F positive definite, {lo}/2^24 I - F not")
