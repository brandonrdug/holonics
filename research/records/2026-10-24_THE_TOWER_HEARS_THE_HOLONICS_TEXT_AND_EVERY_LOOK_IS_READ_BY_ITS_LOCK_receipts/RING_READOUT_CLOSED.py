# Exterior read: closed-form foundings of the bilinear ring readout W(x̂⊗ρ) at the join, against the
# fitted optimum. usage: python3 -I RING_READOUT_CLOSED.py TRAIN HELD HELD_U
import sys, time
import numpy as np
sys.argv += []
exec(open(sys.argv[0].replace("RING_READOUT_CLOSED.py", "RING_READOUT_LAW.py")).read().split("ell_tr, y_tr = offsets")[0])
ell_tr, y_tr = offsets(tr[0], tr[3])
ell_he, y_he = offsets(he[0], he[3])
ptr, phe = feats("top(x)ring", tr), feats("top(x)ring", he)
n, f = ptr.shape
P = np.exp(ell_tr - ell_tr.max(1, keepdims=True)); P /= P.sum(1, keepdims=True)
Y = np.zeros_like(P); Y[np.arange(n), y_tr] = 1.0
res = (Y - P)[:, :C]
# Least squares of the comparison's covector q - p on the face (Q+ M^T).
G = ptr.T @ ptr
ls = np.linalg.solve(G + 1e-9 * np.eye(f), ptr.T @ res)
for k in [1, 2, 4, 8, 16, 32]:
    s = score(phe, ell_he, y_he, k * ls, held_u)
    print(f"least squares x{k:2d}: right {s[0]:3d}/495 bits/digit at U {s[1]:.3f} held bits/byte {s[2]:.3f}", flush=True)
# One Newton step per class with its own curvature p(1-p).
t0 = time.time()
nw = np.zeros((f, C))
for c in range(C):
    w = P[:, c] * (1 - P[:, c])
    Gc = (ptr * w[:, None]).T @ ptr
    nw[:, c] = np.linalg.solve(Gc + 1e-9 * np.eye(f), ptr.T @ res[:, c])
s = score(phe, ell_he, y_he, nw, held_u)
print(f"newton per class: right {s[0]:3d}/495 bits/digit at U {s[1]:.3f} held bits/byte {s[2]:.3f} ({time.time()-t0:.0f} s)", flush=True)
t0 = time.time()
Wt = fit(ptr, ell_tr, y_tr, 1500, 0.02)
s = score(phe, ell_he, y_he, Wt, held_u)
print(f"fitted 1500: right {s[0]:3d}/495 bits/digit at U {s[1]:.3f} held bits/byte {s[2]:.3f} ({time.time()-t0:.0f} s)", flush=True)
