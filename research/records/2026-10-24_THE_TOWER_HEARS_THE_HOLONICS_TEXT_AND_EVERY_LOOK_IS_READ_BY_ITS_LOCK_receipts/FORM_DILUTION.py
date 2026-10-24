"""Where the one complex form's share is lost. The form c = (a^T s)(b^T x) (char/ideal_quiet.txt)
reads a sum's units at B in 475 of 495 held out, and the founding's own measure gives it 4 per mille
of the whole training text's canonical tension. Here: (1) its share counted at the sums' B cells
alone (the covector read at the probe cells of the training equation block, eight parts each from
rest, first sections left out; Y = sum yy^T of the whole training text, as CROSSING_CEILING.py),
beside the exact crossing chi_1(a0) chi_1(b0) and a lookup by c0; (2) the form's within-class
energy over the whole text (from the training moments' per-class sums) against its energy at those
B cells: the cells where the form reads nothing still enter its Gram."""
import importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
line = open("char/ideal_quiet.txt").read().split("\n")[1]
fld = {k: v for k, v in (f.split("=", 1) for f in line.split()[2:])}
a = np.array([[int(x) for x in fld["a"].split(",")], [int(x) for x in fld["ai"].split(",")]], dtype=float)
b = np.array([[int(x) for x in fld["b"].split(",")], [int(x) for x in fld["bi"].split(",")]], dtype=float)
theta = open("hcont2/STATE.0").read().split("\n")[1].split(" ")
hats = np.hstack([np.array([int(v) for v in theta[:256*64]], dtype=float).reshape(256, 64), np.full((256, 1), 65536.0)])
beta = (hats @ b[0]) + 1j * (hats @ b[1])
# whole-text moments
L = open("situated5/train.moments").read().split("\n")
v = [int(x) for x in L[1].split()[1].split(",")]
Y = np.zeros((64, 64)); k = 0
for i in range(64):
    for j in range(i, 64):
        Y[i, j] = Y[j, i] = v[k] / 2**48; k += 1
Yi = np.linalg.inv(Y)
energy_whole, energy_digits = 0.0, 0.0
iu = np.triu_indices(128)
for l in L[2:]:
    if not l.startswith("CLASS "): continue
    p = l.split(); u = int(p[1]); n = int(p[2][2:])
    s = np.array([int(x) for x in p[3][2:].split(",")], dtype=float)
    q = np.zeros((128, 128)); q[iu] = [int(x) for x in p[5][2:].split(",")]; q = q + q.T - np.diag(np.diag(q))
    cq = q - np.outer(s, s) / n          # within-class second moment of the face
    e = (a[0] @ cq @ a[0] + a[1] @ cq @ a[1]) * abs(beta[u])**2   # sum |c - mean|^2 over the class
    energy_whole += e
    if 48 <= u <= 57: energy_digits += e
# the B cells: face from the full modes read (before / 2^8), covector from the probe-cell read
cs, ys, cls, keys = [], [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    role, info = tm.probe_roles(text)
    face = {i: np.round(np.array([v for m in lev[0] for v in m[:2]], dtype=float) / 2**8) for i, _, _, lev in tm.parse(f"char/block{c}_full.txt", True)}
    for l in open(f"situated/cov/block{c}.txt"):
        p = l.split(); i = int(p[1])
        if i < 128 or i not in face: continue
        f = info[i + 1]
        pa = face[i] @ a[0] + 1j * (face[i] @ a[1])
        cs.append(pa * beta[int(p[2])]); ys.append(np.array([int(x) for x in p[3:]], dtype=float) / 2**24)
        cls.append(int(p[2])); keys.append(f)
cs, ys, cls = np.array(cs), np.array(ys), np.array(cls)
def centre(z):
    out = z.copy()
    for u in set(cls):
        m = cls == u; out[m] = z[m] - z[m].mean(0)
    return out
yc = centre(ys)
def share(C):
    Cc = centre(C)
    R, G = Cc.T @ yc, Cc.T @ Cc
    return np.trace(Yi @ R.T @ np.linalg.solve(G, R))
form = np.stack([cs.real, cs.imag], 1)
exact = np.exp(2j*np.pi*np.array([k[1] + k[2] for k in keys])/10)
energy_b = np.sum(np.abs(centre(cs[:, None])[:, 0])**2)
print(f"B cells {len(cs)}")
print(f"share at the B cells alone: the form {1000*share(form):.2f}, the exact crossing chi_1(a0)chi_1(b0) {1000*share(np.stack([exact.real, exact.imag],1)):.2f}, a lookup by c0 {1000*share(np.eye(10)[[k[3] for k in keys]]):.2f} per mille of the text's canonical tension")
print(f"the form's within-class energy: whole text {energy_whole:.4g}, its ten digit classes {energy_digits:.4g} ({1000*energy_digits/energy_whole:.0f} per mille), the sums' B cells {energy_b:.4g} ({1000*energy_b/energy_whole:.1f} per mille of the whole)")
# (3) is the sums' B cell an antinode of the tension? the whitened energy y^T Y^-1 y a cell, against
# the whole text's mean (tr(Y^-1 sum yy^T) / N = 64 / N), and the crossing's part of the B cells' own
N = int(L[0].split("cells=")[1].split()[0])
per_cell = np.einsum("ij,jk,ik->i", ys, Yi, ys)
per_cell_c = np.einsum("ij,jk,ik->i", yc, Yi, yc)
print(f"whitened tension a B cell: mean {per_cell.mean()*N/64:.2f} times the text's mean cell (within its class {per_cell_c.mean()*N/64:.2f}); the B cells hold {1000*per_cell.sum()/64:.2f} per mille of the text's tension; the exact crossing is {1000*share(np.stack([exact.real, exact.imag],1))/(per_cell_c.sum()):.0f} per mille of the B cells' within-class tension")
