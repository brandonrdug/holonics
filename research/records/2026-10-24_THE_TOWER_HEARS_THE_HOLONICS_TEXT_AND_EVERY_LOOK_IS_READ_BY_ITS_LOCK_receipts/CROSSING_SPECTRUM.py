"""How the crossing's canonical share at B spreads over tension directions: eigenvalues of
Y^{-1/2} (Σ_g n_g d_g d_gᵀ) Y^{-1/2}, d_g the lookup's group mean less the arriving class's mean."""
import collections, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
L = open('situated5/train.moments').read().split('\n', 2)
v = [int(x) for x in L[1].split()[1].split(',')]
Y = np.zeros((64, 64)); k = 0
for i in range(64):
    for j in range(i, 64):
        Y[i, j] = Y[j, i] = v[k] / 2**48; k += 1
w, V = np.linalg.eigh(Y); Yh = V @ np.diag(w ** -0.5) @ V.T
for key_name, key_of in (("op,a0,b0", lambda f: (f[0], f[1], f[2])), ("op,c0", lambda f: (f[0], f[3]))):
    groups, cls = collections.defaultdict(list), collections.defaultdict(list)
    for c in range(8):
        text = open(f'modes/block{c}.txt', 'rb').read()
        role, info = tm.probe_roles(text)
        for l in open(f'situated/cov/block{c}.txt'):
            p = l.split(); i = int(p[1])
            if i < 128 or "B" not in role.get(i + 1, ()): continue
            y = np.array([int(x) for x in p[3:]], dtype=float) / 2**24
            groups[(int(p[2]),) + key_of(info[i + 1])].append(y); cls[int(p[2])].append(y)
    cm = {u: np.mean(ys, axis=0) for u, ys in cls.items()}
    M = np.zeros((64, 64))
    for g, ys in groups.items():
        d = Yh @ (np.mean(ys, axis=0) - cm[g[0]]); M += len(ys) * np.outer(d, d)
    e = np.sort(np.linalg.eigvalsh(M))[::-1]
    print(key_name, "total", round(1000 * e.sum(), 2), "top12 per mille", [round(1000 * x, 2) for x in e[:12]])
