# Exterior read: does a field whose transports depend on the symbol, located online by the
# one-step deposition covector, read conjunctions that a shared-transport field cannot?
#   x_(t+1) = U_(u_t) x_t + b_(u_t)            ("pumped": one U per symbol; "shared": one U for all)
#   p_t = softmax(W [x_t, frame phase])        readout at every cell, scored before learning that cell
#   lambda_t = W_x^T (p_t - e_(u_t))            covector at the face
#   dU_(u_(t-1)) = -eta lambda_t x_(t-1)^T,  db_(u_(t-1)) = -eta lambda_t,  dW = -eta f_t (p_t - e)^T
# The deposition reaches back one cell only (no tape). Each U keeps max row sum <= rho (stability).
import sys, time, resource, numpy as np
t0 = time.time()
mode, n, eta, rho, limit = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
data = b"".join(open(p, 'rb').read() for p in sys.argv[6:])
d = [x for b in data for x in (b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3)]
N = min(len(d), limit); cut = int(N * 0.8) // 4 * 4
g = np.random.default_rng(20261022)
K = 4 if mode == "pumped" else 1
U = np.stack([rho * np.linalg.qr(g.standard_normal((n, n)))[0] / np.sqrt(n) for _ in range(K)])
B = g.standard_normal((4, n)) * 0.1
W = np.zeros((n + 4, 4))
x = np.zeros(n); xp = np.zeros(n); up = 0
f = np.zeros(n + 4); I4 = np.eye(4)
tr_bits = 0.0; te_bits = 0.0; LN2 = np.log(2.0)
for t in range(N):
    u = d[t]
    f[:n] = x; f[n:] = I4[t % 4]
    z = f @ W; z -= z.max(); p = np.exp(z); p /= p.sum()
    lb = -np.log(p[u]) / LN2
    if t < cut:
        tr_bits += lb
        p[u] -= 1.0
        lam = W[:n] @ p
        W -= eta * np.outer(f, p)
        if t > 0:
            k = up if K == 4 else 0
            U[k] -= eta * np.outer(lam, xp)
            s = np.abs(U[k]).sum(1); s = np.maximum(s / rho, 1.0); U[k] /= s[:, None]
            B[up] -= eta * lam
    else:
        te_bits += lb
    xp = x; up = u
    x = U[u if K == 4 else 0] @ x + B[u]
print("%-6s n=%2d eta=%g rho=%.2f cells %d: online train %.3f, held-out %.3f bits/digit  (%.1f s, %.2f us/cell, peak %d MiB)" % (
    mode, n, eta, rho, N, tr_bits / cut, te_bits / (N - cut), time.time() - t0,
    1e6 * (time.time() - t0) / N, resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024), flush=True)
