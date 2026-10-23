# Exterior read: the rank, at tolerance, of the context-to-future block of a base-four byte stream.
# Context = last K digits and the next digit's frame phase; future = the next 1, 2 and 3 digits.
# A rank-r linear readout of an r-dimensional state reaches at best the rank-r projection, so the
# bits at rank r bound from below the modes a symbol-driven linear field needs to reach them.
import sys, time, numpy as np
t0 = time.time()
K = int(sys.argv[1]); paths = sys.argv[2:]
data = b"".join(open(p, 'rb').read() for p in paths)
d = np.array([x for b in data for x in (b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3)], dtype=np.int64)
n = len(d); cut = int(n * 0.8) // 4 * 4
def contexts(lo, hi):
    i = np.arange(max(lo, K), hi - 2)
    c = np.zeros(len(i), dtype=np.int64)
    for j in range(1, K + 1): c = c * 4 + d[i - j]
    return i, c * 4 + (i % 4)
C = 4 ** K * 4
i, c = contexts(0, cut)
blocks = []
for L in (1, 2, 3):
    s = np.zeros(len(i), dtype=np.int64)
    for j in range(L): s = s * 4 + d[i + j]
    cnt = np.bincount(c * 4 ** L + s, minlength=C * 4 ** L).reshape(C, 4 ** L).astype(float)
    blocks.append((cnt + 0.5) / (cnt.sum(1, keepdims=True) + 0.5 * 4 ** L))
F = np.hstack(blocks)                       # contexts x 84 conditional future probabilities
nc = np.bincount(c, minlength=C).astype(float)
seen = nc > 0
w = np.sqrt(nc[seen])[:, None]
U, S, Vt = np.linalg.svd(F[seen] * w, full_matrices=False)
energy = np.cumsum(S ** 2) / np.sum(S ** 2)
print("train contexts seen %d of %d; digits %d" % (seen.sum(), C, n))
print("singular values (first 12):", " ".join("%.3g" % x for x in S[:12]))
for r in (1, 2, 4, 8, 16, 32, 64, 84):
    print("  rank %2d keeps %.4f of the weighted energy" % (r, energy[min(r, len(S)) - 1]))
# phase-only fallback for contexts unseen in training
ph = np.bincount((i % 4) * 4 + d[i], minlength=16).reshape(4, 4) + 0.5
ph = ph / ph.sum(1, keepdims=True)
ti, tc = contexts(cut, n)
y = d[ti]; seen_idx = -np.ones(C, dtype=np.int64); seen_idx[np.nonzero(seen)[0]] = np.arange(seen.sum())
def bits(r):
    P = np.empty((len(ti), 4))
    k = seen_idx[tc]; hit = k >= 0
    if r is None:
        Pr = F[seen][:, :4]
    else:
        Pr = ((U[:, :r] * S[:r]) @ Vt[:r, :4]) / w
    Ph = np.clip(Pr[k[hit]], 1e-6, None)
    P[hit] = Ph / Ph.sum(1, keepdims=True)
    P[~hit] = ph[ti[~hit] % 4]
    return -np.log2(P[np.arange(len(y)), y]).mean(), hit.mean()
for r in (1, 2, 4, 8, 16, 32, 64, None):
    b, h = bits(r)
    print("held-out bits/digit at rank %-4s %.3f  (test contexts seen in training %.3f)" % ("full" if r is None else r, b, h))
print("wall %.1f s" % (time.time() - t0))
