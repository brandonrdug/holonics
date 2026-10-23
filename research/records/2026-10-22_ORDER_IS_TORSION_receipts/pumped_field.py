# Exterior read: a damped linear field x_(t+1) = A_(u_t) x_t + b_(u_t) with a fixed random constitution
# and a learned softmax readout of [x_t, frame phase]. "shared": one linear part A for every symbol
# (the input only adds). "pumped": the linear part depends on the symbol (the input modulates the
# constitution). Same dimension, same damping, same readout; only the dependence of A on u differs.
import sys, time, resource, numpy as np
t0 = time.time()
mode, r, rho, iters = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
data = b"".join(open(p, 'rb').read() for p in sys.argv[5:])
d = np.array([x for b in data for x in (b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3)], dtype=np.int64)
n = len(d); cut = int(n * 0.8) // 4 * 4
g = np.random.default_rng(20261022)
def orth(): return np.linalg.qr(g.standard_normal((r, r)))[0]
Q = [orth()] * 4 if mode == "shared" else [orth() for _ in range(4)]
A = np.stack([rho * q for q in Q]); B = g.standard_normal((4, r)) / np.sqrt(r)
X = np.empty((n, r), dtype=np.float32); x = np.zeros(r)
for t in range(n):
    X[t] = x                                   # state before reading d[t]: predicts d[t]
    x = A[d[t]] @ x + B[d[t]]
F = np.hstack([X, np.eye(4, dtype=np.float32)[np.arange(n) % 4]])
t1 = time.time()
Xtr, ytr, Xte, yte = F[16:cut:2], d[16:cut:2], F[cut:], d[cut:]  # train on every second cell
W = np.zeros((F.shape[1], 4), dtype=np.float32); m = np.zeros_like(W); v = np.zeros_like(W)
for k in range(1, iters + 1):
    z = Xtr @ W; z -= z.max(1, keepdims=True); p = np.exp(z); p /= p.sum(1, keepdims=True)
    p[np.arange(len(ytr)), ytr] -= 1; gW = Xtr.T @ p / len(ytr)
    m = .9 * m + .1 * gW; v = .999 * v + .001 * gW * gW
    W -= 0.05 * (m / (1 - .9 ** k)) / (np.sqrt(v / (1 - .999 ** k)) + 1e-9)
z = Xte @ W; z -= z.max(1, keepdims=True); lp = z - np.log(np.exp(z).sum(1, keepdims=True))
print("%-6s r=%3d rho=%.2f: held-out %.3f bits/digit  (state %.1f s, readout %d steps %.1f s)" % (
    mode, r, rho, -lp[np.arange(len(yte)), yte].mean() / np.log(2), t1 - t0, iters, time.time() - t1), "peak %d MiB" % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024), flush=True)
