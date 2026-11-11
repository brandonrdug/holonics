#!/usr/bin/env python3
"""Check: on a quadratic code with lap noise, the cosine of two successive lap displacements is c_s - eta*Hbar,
and the expected fall of the code over the first of the two laps is greatest where that cosine is zero."""
import numpy as np
rng = np.random.default_rng(7)
n = 400
H = np.diag(rng.uniform(0.2, 3.0, n))           # curvatures
x0 = rng.normal(0, 1.0, n)                       # a state on a slope
g = H @ x0
sig = rng.uniform(0.5, 2.5, n)                   # noise scale by direction
Sigma = sig**2
cs = (g @ g) / (g @ g + Sigma.sum())
Hbar = (g @ H @ g + (np.diag(H) * Sigma).sum()) / (g @ g + Sigma.sum())
print(f"c_s={cs:.4f} Hbar={Hbar:.4f} eta*={cs/Hbar:.4f}")
L = lambda x: 0.5 * x @ H @ x
for eta in [0.02, 0.05, 0.1, 0.2, cs / Hbar, 0.4, 0.6]:
    num = den = fall = 0.0
    T = 4000
    for _ in range(T):
        d1 = -eta * (g + sig * rng.normal(size=n))
        x1 = x0 + d1
        d2 = -eta * (H @ x1 + sig * rng.normal(size=n))
        num += d1 @ d2
        den += np.sqrt((d1 @ d1) * (d2 @ d2))
        fall += L(x0) - L(x1)
    print(f"eta={eta:.4f} cos={num/den:+.4f} predicted={cs - eta*Hbar:+.4f} fall={fall/T:+.3f} predicted_fall={(g@g+Sigma.sum())*(eta*cs-0.5*eta*eta*Hbar):+.3f}")
