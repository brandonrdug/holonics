"""The most any crossing of a sum's operands at B could carry under the founding's own criterion:
the canonical share tr(Y⁻¹ Σ_g n_g ȳ_g ȳ_gᵀ) of a lookup of the input covector at B by (operation,
a0, b0), centred on the arriving class's mean over those cells, with Y = Σyyᵀ over the whole
training text (train.moments). An exterior reading; the B cells are the eight parts of the
equation block, each read from rest (cells in the first section of a part are left out)."""
import collections, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
L = open('situated5/train.moments').read().split('\n', 2)
N = int(L[0].split('cells=')[1].split()[0])
v = [int(x) for x in L[1].split()[1].split(',')]
Y = np.zeros((64, 64)); k = 0
for i in range(64):
    for j in range(i, 64):
        Y[i, j] = Y[j, i] = v[k] / 2**48; k += 1
Yi = np.linalg.inv(Y)
for roles in ("B", "A", "E", "U"):
    for key_of in (("op,a0,b0", lambda f: (f[0], f[1], f[2])), ("op,c0", lambda f: (f[0], f[3]))):
        groups, cls = collections.defaultdict(list), collections.defaultdict(list)
        for c in range(8):
            text = open(f'modes/block{c}.txt', 'rb').read()
            role, info = tm.probe_roles(text)
            for l in open(f'situated/cov/block{c}.txt'):
                p = l.split(); i = int(p[1])
                if i < 128 or roles not in role.get(i + 1, ()): continue
                y = np.array([int(x) for x in p[3:]], dtype=float) / 2**24
                f = info[i + 1]
                groups[(int(p[2]),) + key_of[1](f)].append(y); cls[int(p[2])].append(y)
        cm = {u: np.mean(ys, axis=0) for u, ys in cls.items()}
        s = 0.0
        for g, ys in groups.items():
            d = np.mean(ys, axis=0) - cm[g[0]]
            s += len(ys) * d @ Yi @ d
        n = sum(len(x) for x in groups.values())
        print(f"{roles} by {key_of[0]}: cells={n} groups={len(groups)} ceiling share={1000 * s:.2f} per mille of the text's canonical tension")
