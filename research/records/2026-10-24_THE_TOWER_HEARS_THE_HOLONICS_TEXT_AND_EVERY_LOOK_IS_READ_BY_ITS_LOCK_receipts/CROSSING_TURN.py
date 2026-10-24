"""Whether the tension at B turns with the sum's units: the whitened input covector at B, its
arriving class's mean removed, averaged per c0; the plane of the top two directions; each c0's
angle and radius there, and the fit of the angles to a character d -> 2 pi k d / 10."""
import collections, importlib.util, cmath, math
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
L = open('situated5/train.moments').read().split('\n', 2)
v = [int(x) for x in L[1].split()[1].split(',')]
Y = np.zeros((64, 64)); k = 0
for i in range(64):
    for j in range(i, 64):
        Y[i, j] = Y[j, i] = v[k] / 2**48; k += 1
w, V = np.linalg.eigh(Y); Yh = V @ np.diag(w ** -0.5) @ V.T
rows, cls = [], collections.defaultdict(list)
for c in range(8):
    text = open(f'modes/block{c}.txt', 'rb').read()
    role, info = tm.probe_roles(text)
    for l in open(f'situated/cov/block{c}.txt'):
        p = l.split(); i = int(p[1])
        if i < 128 or "B" not in role.get(i + 1, ()) or info[i + 1][0] != '+': continue
        y = Yh @ (np.array([int(x) for x in p[3:]], dtype=float) / 2**24)
        f = info[i + 1]; rows.append((int(p[2]), f[1], f[2], f[3], y)); cls[int(p[2])].append(y)
cm = {u: np.mean(ys, axis=0) for u, ys in cls.items()}
by = collections.defaultdict(list)
for u, a0, b0, c0, y in rows: by[c0].append(y - cm[u])
means = {d: np.mean(by[d], axis=0) for d in sorted(by)}
D = np.array([means[d] * math.sqrt(len(by[d])) for d in sorted(by)])
U, S, Vt = np.linalg.svd(D, full_matrices=False)
print("sums", len(rows), "per c0", {d: len(by[d]) for d in sorted(by)})
print("singular values^2 per mille of N:", [round(1000 * s * s / 1789108, 2) for s in S[:6]])
for pair in ((0, 1), (2, 3)):
    z = {d: complex(means[d] @ Vt[pair[0]], means[d] @ Vt[pair[1]]) for d in means}
    print("plane", pair, " ".join(f"{d}:{abs(z[d]):.3f}@{math.degrees(cmath.phase(z[d])):.0f}" for d in sorted(z)))
    for kk in range(1, 6):
        r = abs(sum(z[d] * cmath.exp(-2j * math.pi * kk * d / 10) for d in z)) / sum(abs(z[d]) for d in z)
        rc = abs(sum(z[d] * cmath.exp(2j * math.pi * kk * d / 10) for d in z)) / sum(abs(z[d]) for d in z)
        print(f"  character k={kk}: alignment {r:.3f} (reversed {rc:.3f})")
