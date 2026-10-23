# Exterior read of the design thread's field: K complex modes, each moved by the symbol,
#   z_k' = lam[k, s] z_k + beta[k, s],  |lam| <= rho,
# read by a softmax of [Re z, Im z, frame phase]; learned online with the forward jet
#   J_lam[k, a]' = lam[k, s] J_lam[k, a] + [s = a] z_k,   J_beta[k, a]' = lam[k, s] J_beta[k, a] + [s = a],
# ("shared" uses one lam for every symbol: the additive-entry control)
# deposited each cell with the complex covector g_k (dL/dRe z + i dL/dIm z):
#   d lam[k, a] = -eta g_k conj(J_lam[k, a])   (turn and boost together; "radial" keeps only the real part)
import sys, time, resource, numpy as np
t0 = time.time()
mode, K, eta, rho, limit = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
data = b"".join(open(p, 'rb').read() for p in sys.argv[6:])
d = [x for b in data for x in (b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3)]
N = min(len(d), limit); cut = int(N * 0.8) // 4 * 4
g = np.random.default_rng(20261022)
lam = rho * np.sqrt(g.uniform(0.25, 1, (K, 4))) * np.exp(2j * np.pi * g.uniform(0, 1, (K, 4)))
beta = (g.standard_normal((K, 4)) + 1j * g.standard_normal((K, 4))) * 0.1
W = np.zeros((2 * K + 4, 4))
z = np.zeros(K, complex); Jl = np.zeros((K, 4), complex); Jb = np.zeros((K, 4), complex)
f = np.zeros(2 * K + 4); I4 = np.eye(4); LN2 = np.log(2.0)
tr = te = 0.0
for t in range(N):
    u = d[t]
    f[:K] = z.real; f[K:2 * K] = z.imag; f[2 * K:] = I4[t % 4]
    q = f @ W; q -= q.max(); p = np.exp(q); p /= p.sum()
    lb = -np.log(p[u]) / LN2
    if t < cut:
        tr += lb
        p[u] -= 1.0
        gr = W[:2 * K] @ p; gk = gr[:K] + 1j * gr[K:]
        W -= eta * np.outer(f, p)
        dl = gk[:, None] * np.conj(Jl); db = gk[:, None] * np.conj(Jb)
        if mode == "radial": dl = dl.real
        lam -= eta * dl; beta -= eta * db
        a = np.abs(lam); lam = np.where(a > rho, lam * (rho / np.maximum(a, 1e-300)), lam)
    else:
        te += lb
    ul = 0 if mode == "shared" else u        # shared: one turn for every symbol (lag-residue control)
    ls = lam[:, ul]
    Jl *= ls[:, None]; Jl[:, ul] += z
    Jb *= ls[:, None]; Jb[:, u] += 1.0
    z = ls * z + beta[:, u]
print("%-7s K=%2d eta=%g rho=%.3f cells %d: online train %.3f, held-out %.3f bits/digit  (%.1f s, %.2f us/cell, peak %d MiB)" % (
    mode, K, eta, rho, N, tr / cut, te / (N - cut), time.time() - t0,
    1e6 * (time.time() - t0) / N, resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024), flush=True)
