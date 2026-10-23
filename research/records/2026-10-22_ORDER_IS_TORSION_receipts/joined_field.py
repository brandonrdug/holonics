# Exterior read: does the design's field add anything over a context tree when joined with it?
# Tree: Krichevsky-Trofimov counts on (frame phase, last 6 digits), read before the cell is counted.
# Joined face: p = softmax(log q_tree + W f), f = [Re z, Im z]; the field is the design's
#   z_k' = lam[k, s] z_k + beta[k, s] ("selected"), or one lam for every symbol ("shared"),
# learned online with the forward jet and the complex covector g = dL/dRe z + i dL/dIm z.
# "tree" scores the tree alone. Every cell is scored before it is learned (prequential).
import sys, time, resource, numpy as np
t0 = time.time()
mode, K, eta, rho, limit = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
data = b"".join(open(p, 'rb').read() for p in sys.argv[6:])
d = [x for b in data for x in (b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3)]
N = min(len(d), limit)
cnt = np.zeros((4 * 4 ** 6, 4))
g = np.random.default_rng(20261022)
lam = rho * np.sqrt(g.uniform(0.25, 1, (K, 4))) * np.exp(2j * np.pi * g.uniform(0, 1, (K, 4)))
beta = (g.standard_normal((K, 4)) + 1j * g.standard_normal((K, 4))) * 0.1
W = np.zeros((2 * K, 4))
z = np.zeros(K, complex); Jl = np.zeros((K, 4), complex); Jb = np.zeros((K, 4), complex)
f = np.zeros(2 * K); LN2 = np.log(2.0); ctx = 0; bits = 0.0; span = []; acc = 0.0
for t in range(N):
    u = d[t]
    c = (t % 4) * 4096 + ctx
    q = (cnt[c] + 0.5) / (cnt[c].sum() + 2.0)
    if mode == "tree":
        p = q
    else:
        f[:K] = z.real; f[K:] = z.imag
        a = np.log(q) + f @ W; a -= a.max(); p = np.exp(a); p /= p.sum()
    lb = -np.log(p[u]) / LN2; bits += lb; acc += lb
    if (t + 1) % 500000 == 0: span.append(acc / 500000); acc = 0.0
    cnt[c, u] += 1.0
    ctx = (ctx * 4 + u) % 4096
    if mode == "tree": continue
    p = p.copy(); p[u] -= 1.0
    gr = W @ p; gk = gr[:K] + 1j * gr[K:]
    W -= eta * np.outer(f, p)
    lam -= eta * gk[:, None] * np.conj(Jl); beta -= eta * gk[:, None] * np.conj(Jb)
    m = np.abs(lam); lam = np.where(m > rho, lam * (rho / np.maximum(m, 1e-300)), lam)
    ul = 0 if mode == "shared" else u
    ls = lam[:, ul]
    Jl *= ls[:, None]; Jl[:, ul] += z
    Jb *= ls[:, None]; Jb[:, u] += 1.0
    z = ls * z + beta[:, u]
print("%-8s K=%2d eta=%g rho=%.3f cells %d: %.4f bits/digit; per 500k cells %s  (%.1f s, %.2f us/cell, peak %d MiB)" % (
    mode, K, eta, rho, N, bits / N, " ".join("%.4f" % s for s in span), time.time() - t0,
    1e6 * (time.time() - t0) / N, resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024), flush=True)
