# Exterior read: does a quadratic (Born) face on the design's diagonal modes read the pairwise
# conjunctions that a linear face cannot?
#   z_k' = lam[k, s] z_k + beta[k, s]          the design's modes, turns selected by the symbol
#   linear face:    a_c = w_c . [Re z, Im z] (+ frame bias, or + log q_tree when joined)
#   quadratic face: a_c += z^H H_c z, H_c Hermitian (the Born read of the density z z^H)
# Learning: W and H_c by the face's covector p - e_u; lam, beta by the forward jets with the
# complex covector g = dL/dRe z + i dL/dIm z = W-part + 2 sum_c (p_c - e_c) H_c z.
# "alone": online over the first 80%, held out frozen.  "tree": joined with KT counts on
# (frame phase, last 6 digits), every cell scored before it is learned.
import sys, time, resource, numpy as np
t0 = time.time()
face, join, K, eta, rho, limit = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6])
data = b"".join(open(p, 'rb').read() for p in sys.argv[7:])
d = [x for b in data for x in (b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3)]
N = min(len(d), limit); cut = N if join == "tree" else int(N * 0.8) // 4 * 4
g = np.random.default_rng(20261022)
lam = rho * np.sqrt(g.uniform(0.25, 1, (K, 4))) * np.exp(2j * np.pi * g.uniform(0, 1, (K, 4)))
beta = (g.standard_normal((K, 4)) + 1j * g.standard_normal((K, 4))) * 0.1
W = np.zeros((2 * K + 4, 4)); H = np.zeros((4, K, K), complex); etaq = eta / 4
cnt = np.zeros((4 * 4 ** 6, 4)); ctx = 0
z = np.zeros(K, complex); Jl = np.zeros((K, 4), complex); Jb = np.zeros((K, 4), complex)
f = np.zeros(2 * K + 4); I4 = np.eye(4); LN2 = np.log(2.0)
tr = te = 0.0; span = []; acc = 0.0
for t in range(N):
    u = d[t]
    f[:K] = z.real; f[K:2 * K] = z.imag; f[2 * K:] = I4[t % 4]
    a = f @ W
    if face == "quad":
        Hz = H @ z; a = a + np.real(np.conj(z) @ Hz.T)
    if join == "tree":
        c = (t % 4) * 4096 + ctx
        q = (cnt[c] + 0.5) / (cnt[c].sum() + 2.0)
        a = a + np.log(q)
        cnt[c, u] += 1.0; ctx = (ctx * 4 + u) % 4096
    a = a - a.max(); p = np.exp(a); p /= p.sum()
    lb = -np.log(p[u]) / LN2; acc += lb
    if (t + 1) % 500000 == 0: span.append(acc / 500000); acc = 0.0
    if t < cut:
        tr += lb
        p[u] -= 1.0
        gr = W[:2 * K] @ p; gk = gr[:K] + 1j * gr[K:]
        W -= eta * np.outer(f, p)
        if face == "quad":
            gk = gk + 2.0 * (p @ Hz)
            H -= etaq * p[:, None, None] * np.outer(z, np.conj(z))[None]
        lam -= eta * gk[:, None] * np.conj(Jl); beta -= eta * gk[:, None] * np.conj(Jb)
        m = np.abs(lam); lam = np.where(m > rho, lam * (rho / np.maximum(m, 1e-300)), lam)
    else:
        te += lb
    ls = lam[:, u]
    Jl *= ls[:, None]; Jl[:, u] += z
    Jb *= ls[:, None]; Jb[:, u] += 1.0
    z = ls * z + beta[:, u]
held = (" held-out %.4f" % (te / (N - cut))) if N > cut else ""
print("%-4s %-5s K=%2d eta=%g rho=%.3f cells %d: online %.4f%s bits/digit; per 500k %s  (%.1f s, %.2f us/cell, peak %d MiB)" % (
    face, join, K, eta, rho, N, tr / cut, held, " ".join("%.4f" % s for s in span), time.time() - t0,
    1e6 * (time.time() - t0) / N, resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024), flush=True)
