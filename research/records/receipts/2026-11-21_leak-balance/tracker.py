#!/usr/bin/env python3
"""A store that follows a level, and a pumped carry circle, on a planted drive (host arithmetic; no state of the machine is read).

Part 1: the tracker Q(t) = Q(t-1) + delta n(t), n(t) = b(t) - Q(t-1), on a drive b of correlation phi a site.
        The correlation of successive news, from the news's weights on the drive's own news, and its zero delta* = 2 phi/(1 + phi).
Part 2: the six medians of 1 - |gamma| the engineering thread read at d times 2^(-k) (gates_lighter.txt) against the pumped gate's
        form gamma = ghat/(1 + d + n) (crates/engine/src/carry.rs, carry_gate_pumped).
Part 3: a pumped circle Q' = gamma Q + eta conj(Q) + kappa b on a white complex Gaussian drive, its news read as the engineering
        thread's test reads it, u(t) = Q(t) - ghat Q(t-1), pooled as sum Re(conj(u(t)) ghat u(t-1)) / sum |u(t)||u(t-1)|.
Part 4: the charge's scale kappa/(1 - hold) by axis as d falls, n standing.
"""
import math
import numpy as np


def rho1(delta, phi, n=4000):
    """Correlation of successive news: n = (1 - L)/((1 - aL)(1 - phi L)) e, a = 1 - delta."""
    a = 1.0 - delta
    x, pj, c = 0.0, 1.0, []
    for _ in range(n):
        x = a * x + pj
        c.append(x)
        pj *= phi
    psi = [c[0]] + [c[j] - c[j - 1] for j in range(1, n)]
    g0 = sum(p * p for p in psi)
    g1 = sum(psi[j] * psi[j + 1] for j in range(n - 1))
    return g1 / g0


print("PART 1  the tracker's successive news, correlation by gain delta = 0.2 0.4 0.6 0.8, and its zero")
for phi in (0.0, 0.035, 0.2, 0.4, 0.6, 0.8):
    rest = 2 * phi / (1 + phi)
    at = rho1(max(rest, 1e-9), phi)
    print("TRACKER phi=%.3f corr=[%s] white=-delta/2=[%s] rest=2phi/(1+phi)=%.3f corr_at_rest=%+.5f" % (
        phi, " ".join("%+.3f" % rho1(d, phi) for d in (0.2, 0.4, 0.6, 0.8)),
        " ".join("%+.3f" % (-d / 2) for d in (0.2, 0.4, 0.6, 0.8)), rest, at))
print("TRACKER guess_G1 (unpumped, delta=d/(1+d), d=1.5*2^-k, phi=0.035) = [%s]" % " ".join(
    "%+.3f" % rho1(1.5 * 2.0 ** -k / (1 + 1.5 * 2.0 ** -k), 0.035) for k in range(6)))

print("PART 2  the medians of 1 - |gamma| against the pumped form")
read = [0.600, 0.506, 0.435, 0.392, 0.368, 0.356]
best = None
for d0 in [x / 100 for x in range(60, 151)]:
    for n in [x / 100 for x in range(0, 91)]:
        worst = max(abs(1 - 1 / (1 + d0 * 2.0 ** -k + n) - read[k]) for k in range(6))
        if best is None or worst < best[0]:
            best = (worst, d0, n)
worst, d0, n = best
print("PUMPED_FORM read=[%s]" % " ".join("%.3f" % r for r in read))
print("PUMPED_FORM fit d0=%.2f n=%.2f model=[%s] largest_miss=%.3f" % (
    d0, n, " ".join("%.3f" % (1 - 1 / (1 + d0 * 2.0 ** -k + n)) for k in range(6)), worst))
print("PUMPED_FORM unpumped (n=0, d0=1.5) model=[%s]" % " ".join("%.3f" % (1 - 1 / (1 + 1.5 * 2.0 ** -k)) for k in range(6)))
print("PUMPED_FORM gain on the drive kappa/N0 = d/(1+d+n) by k=[%s]" % " ".join(
    "%.3f" % (d0 * 2.0 ** -k / (1 + d0 * 2.0 ** -k + n)) for k in range(6)))

print("PART 3  a pumped circle on a white complex Gaussian drive, the cosine as the test pools it")
rng = np.random.default_rng(20261121)
T = 120000
b = (rng.standard_normal(T) + 1j * rng.standard_normal(T)) / math.sqrt(2)


def pooled(d, nn, pabs, th):
    one = 1.0 + d + nn
    ghat = complex(math.cos(th), math.sin(th))
    g, eta, kap = ghat / one, pabs / one, d / one
    q, u = 0j, np.empty(T, complex)
    for t in range(T):
        qn = g * q + eta * q.conjugate() + kap * b[t]
        u[t] = qn - ghat * q
        q = qn
    num = float(np.sum((np.conj(u[1:]) * ghat * u[:-1]).real))
    den = float(np.sum(np.abs(u[1:]) * np.abs(u[:-1])))
    corr = num / float(np.sum(np.abs(u) ** 2))
    return num / den, corr


print("COSINE read (gates_lighter.txt) k=0..5 = [-0.275 -0.190 -0.125 -0.089 -0.064 -0.060]")
c, r = pooled(d0, 0.0, 0.0, 0.3)
print("COSINE unpumped d=%.2f (gain %.3f): pooled=%+.3f correlation=%+.3f -delta/2=%+.3f ratio=%.3f (4/pi=%.3f)" % (
    d0, d0 / (1 + d0), c, r, -d0 / (1 + d0) / 2, c / r, 4 / math.pi))
for pabs in (n / math.sqrt(2), n):
    for th in (0.0, 0.3, 0.8, 1.5):
        row = [pooled(d0 * 2.0 ** -k, n, pabs, th)[0] for k in range(6)]
        print("COSINE pumped n=%.2f |p|=%.2f turn=%.1f k=0..5 = [%s]" % (n, pabs, th, " ".join("%+.3f" % x for x in row)))

print("PART 4  the charge's scale kappa/(N0 (1 - hold)) by axis, n standing (the pump along and across, where the pump beats the turn)")
for pabs in (n / math.sqrt(2), n):
    along, across = [], []
    for k in range(6):
        d = d0 * 2.0 ** -k
        one = 1 + d + n
        along.append((d / one) / (1 - (1 + pabs) / one))
        across.append((d / one) / (1 - (1 - pabs) / one))
    print("SCALE |p|=%.2f along=[%s] across=[%s] across_k0_over_k5=%.1f" % (
        pabs, " ".join("%.3f" % x for x in along), " ".join("%.3f" % x for x in across), across[0] / across[5]))
for pabs in (n / math.sqrt(2), n):
    both = []
    for k in range(6):
        d = d0 * 2.0 ** -k
        one = 1 + d + n
        both.append((d / one) / (1 - math.sqrt(1 - pabs * pabs) / one))
    print("SCALE |p|=%.2f where the turn beats the pump (both multipliers of modulus sqrt(|gamma|^2 - |eta|^2)) both=[%s] k0_over_k5=%.1f" % (
        pabs, " ".join("%.3f" % x for x in both), both[0] / both[5]))
print("SCALE unpumped (n = 0): kappa/(N0 (1 - |gamma|)) = 1 at every d")
