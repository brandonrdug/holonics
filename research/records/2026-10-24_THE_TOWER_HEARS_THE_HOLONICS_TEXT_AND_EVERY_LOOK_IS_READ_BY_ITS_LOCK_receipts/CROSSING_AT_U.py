"""Where the units' error is made: the cell U that codes a true sum's units digit. (1) Does level 0's
state there (before and after the class arriving at U) carry each operand's units as a phase in a
straight-line read, and does the product of the two reads, a form of the state with itself, give the
sum's units? (2) Is U an antinode of the tension, and how much of the tension U receives is the
crossing? Same tower, texts, release, ridge and normalization as CHARACTER_AT_B.py and
FORM_DILUTION.py."""
import importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)

def load(text_path, modes_path, which):
    text = open(text_path, "rb").read()
    role, info = tm.probe_roles(text)
    X, F, I = [], [], []
    for i, _, _, levels in tm.parse(modes_path, True):
        f = info[i + 1]
        assert f[0] == "+" and "U" in role[i + 1] and text[i + 1] - 48 == f[3]
        X.append([v for m in levels[0] for v in m[which:which + 2]]); F.append(f[1:]); I.append(i)
    return np.array(X, dtype=float) / 2**14, np.array(F), I

def ridge(X, Y):
    A = np.hstack([X, np.ones((len(X), 1))])
    W = np.linalg.solve(A.T @ A + np.eye(A.shape[1]), A.T @ Y)
    return lambda Z: np.hstack([Z, np.ones((len(Z), 1))]) @ W

def nearest(z):
    return np.abs(z[:, None] - np.exp(2j*np.pi*np.arange(10)/10)[None, :]).argmin(1)

def indicators(Xtr, ltr, Xte, lte):
    return int((ridge(Xtr, np.eye(10)[ltr])(Xte).argmax(1) == lte).sum())

for name, which in (("before", 0), ("after", 4)):
    parts = [load(f"modes/block{c}.txt", f"char/block{c}_ufull.txt", which) for c in range(8)]
    Xt = np.vstack([p[0] for p in parts]); Ft = np.vstack([p[1] for p in parts])
    Xd, Fd, _ = load("htext2/dev_arithmetic.txt", "char/dev_ufull.txt", which)
    z = {}
    for j, op in ((0, "a0"), (1, "b0")):
        zt, zd = np.exp(2j*np.pi*Ft[:,j]/10), np.exp(2j*np.pi*Fd[:,j]/10)
        f = ridge(Xt, np.stack([zt.real, zt.imag], 1)); pt, pd = f(Xt), f(Xd)
        z[op] = (pt[:,0] + 1j*pt[:,1], pd[:,0] + 1j*pd[:,1])
        sh = 1 - np.sum(np.abs(zd - z[op][1])**2) / np.sum(np.abs(zd - zd.mean())**2)
        print(f"U {name}: {op} indicators {indicators(Xt, Ft[:,j], Xd, Fd[:,j])}, its character's share held out {1000*sh:.0f} per mille, nearest root {int((nearest(z[op][1]) == Fd[:,j]).sum())} of {len(Xd)}")
    ct, cd = z["a0"][0] * z["b0"][0], z["a0"][1] * z["b0"][1]
    Ct, Cd = np.stack([ct.real, ct.imag], 1), np.stack([cd.real, cd.imag], 1)
    print(f"U {name}: c0 by indicators from the state {indicators(Xt, Ft[:,2], Xd, Fd[:,2])}; from the product of the two reads by angle {int((nearest(cd) == Fd[:,2]).sum())}, by the probe's indicator fit {indicators(Ct, Ft[:,2], Cd, Fd[:,2])} of {len(Xd)}")

# the tension at U
L = open("situated5/train.moments").read().split("\n")
N = int(L[0].split("cells=")[1].split()[0])
v = [int(x) for x in L[1].split()[1].split(",")]
Y = np.zeros((64, 64)); k = 0
for i in range(64):
    for j in range(i, 64):
        Y[i, j] = Y[j, i] = v[k] / 2**48; k += 1
Yi = np.linalg.inv(Y)
for r in ("U", "B", "E", "A"):
    ys, cls, keys = [], [], []
    for c in range(8):
        role, info = tm.probe_roles(open(f"modes/block{c}.txt", "rb").read())
        for l in open(f"situated/cov/block{c}.txt"):
            p = l.split(); i = int(p[1])
            if i < 128 or r not in role.get(i + 1, ()) or info[i + 1][0] != "+": continue
            ys.append(np.array([int(x) for x in p[3:]], dtype=float) / 2**24); cls.append(int(p[2])); keys.append(info[i + 1])
    ys, cls = np.array(ys), np.array(cls)
    yc = ys.copy()
    for u in set(cls):
        m = cls == u; yc[m] -= ys[m].mean(0)
    def share(C):
        Cc = C - 0
        for u in set(cls):
            m = cls == u; Cc[m] = C[m] - C[m].mean(0)
        R, G = Cc.T @ yc, Cc.T @ Cc
        return np.trace(Yi @ R.T @ np.linalg.lstsq(G, R, rcond=None)[0])
    ex = np.exp(2j*np.pi*np.array([k[3] for k in keys])/10)
    within = np.einsum("ij,jk,ik->i", yc, Yi, yc).sum()
    whole = np.einsum("ij,jk,ik->i", ys, Yi, ys)
    print(f"{r}: cells {len(ys)}; whitened tension a cell {whole.mean()*N/64:.2f} times the text's mean; within-class tension {1000*within:.1f} per mille (the founding's unit); the exact crossing chi_1(c0) {1000*share(np.stack([ex.real, ex.imag],1)):.2f} ({1000*share(np.stack([ex.real, ex.imag],1))/within:.0f} per mille of the cells' own), a lookup by c0 {1000*share(np.eye(10)[[k[3] for k in keys]]):.2f}")
