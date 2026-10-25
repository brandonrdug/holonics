# Exterior read for choosing the ring's readout law (floats here are a reading, never the machine).
# usage: python3 -I readout_law.py TRAIN.cells HELD.cells HELD_U.cells [ranks]
# Records from `read-tower-cells`: next u32, top 64 i32, rho 2R i32, shares 256 u32 on 2^-32.
import sys, time
import numpy as np

W, A = 64, 256
R2 = 2 * (int(sys.argv[4]) if len(sys.argv) > 4 else 1)
REC = 1 + W + R2 + A


def load(path):
    raw = np.fromfile(path, dtype="<i4").reshape(-1, REC)
    nxt = raw[:, 0].astype(np.int64)
    top = raw[:, 1:1 + W].astype(np.float64)
    rho = raw[:, 1 + W:1 + W + R2].astype(np.float64) / 2 ** 16
    p = raw[:, 1 + W + R2:].view("<u4").astype(np.float64) / 2 ** 32
    return nxt, top, rho, p


tr = load(sys.argv[1])
he = load(sys.argv[2])
held_u = np.array([int(x) for x in open(sys.argv[3]).read().split()])
present = np.unique(np.concatenate([tr[0], he[0]]))
C = len(present)
col = {c: j for j, c in enumerate(present)}


def offsets(nxt, p):
    # The tower's own log-shares on the present classes, the rest lumped as one more class.
    q = np.maximum(p[:, present], 2.0 ** -40)
    rest = np.maximum(1.0 - q.sum(1, keepdims=True), 2.0 ** -40)
    ell = np.log(np.concatenate([q, rest], 1))
    y = np.array([col.get(int(c), C) for c in nxt])
    return ell, y


def unit_rms(x):
    r = np.sqrt((x * x).mean(1, keepdims=True))
    return x / np.maximum(r, 1e-12)


def feats(kind, d, gate=None):
    nxt, top, rho, p = d
    n = len(nxt)
    one = np.ones((n, 1))
    xh = np.concatenate([unit_rms(top), one], 1)
    if kind == "bias":
        return one
    if kind == "ring":
        return np.concatenate([one, rho], 1)
    if kind == "top":
        return xh
    if kind == "top+ring":
        return np.concatenate([xh, rho], 1)
    if kind == "top(x)ring":
        return np.concatenate([xh, (xh[:, :, None] * rho[:, None, :]).reshape(n, -1)], 1)
    if kind == "gate(x)ring":
        g = xh @ gate
        return np.concatenate([one, rho, g[:, None], g[:, None] * rho], 1)
    raise ValueError(kind)


def fit(phi, ell, y, iters, lr):
    # Multinomial logistic readout on the tower's held log-shares (rows only for present classes).
    n, f = phi.shape
    Wt = np.zeros((f, C))
    m = np.zeros_like(Wt)
    v = np.zeros_like(Wt)
    Y = np.zeros((n, C + 1))
    Y[np.arange(n), y] = 1.0
    for k in range(1, iters + 1):
        z = ell.copy()
        z[:, :C] += phi @ Wt
        z -= z.max(1, keepdims=True)
        e = np.exp(z)
        P = e / e.sum(1, keepdims=True)
        g = phi.T @ (P - Y)[:, :C] / n
        m = 0.9 * m + 0.1 * g
        v = 0.999 * v + 0.001 * g * g
        Wt -= lr * (m / (1 - 0.9 ** k)) / (np.sqrt(v / (1 - 0.999 ** k)) + 1e-8)
    return Wt


def score(phi, ell, y, Wt, cells):
    z = ell.copy()
    z[:, :C] += phi @ Wt
    z -= z.max(1, keepdims=True)
    lp = z - np.log(np.exp(z).sum(1, keepdims=True))
    bits = -lp[np.arange(len(y)), y] / np.log(2)
    right = (lp.argmax(1) == y)
    return int(right[cells].sum()), float(bits[cells].mean()), float(bits.mean())


ell_tr, y_tr = offsets(tr[0], tr[3])
ell_he, y_he = offsets(he[0], he[3])
# Landmark gate: least squares of the training U indicator on the top face (a received landmark).
u_tr = np.zeros(len(y_tr))
if len(sys.argv) > 5:
    u_tr[[int(x) for x in open(sys.argv[5]).read().split()]] = 1.0
xh_tr = feats("top", tr)
gate = np.linalg.lstsq(xh_tr, u_tr, rcond=None)[0]
gh = feats("top", he) @ gate
print(f"cells train={len(y_tr)} held={len(y_he)} at U={len(held_u)} classes={C}+rest")
print(f"gate at held U: mean {gh[held_u].mean():.3f}, elsewhere {np.delete(gh, held_u).mean():.3f}")
base = score(np.zeros((len(y_he), 1)), ell_he, y_he, np.zeros((1, C)), held_u)
print(f"tower alone: right {base[0]}/495, bits a digit at U {base[1]:.3f}, held bits a byte {base[2]:.3f}")
for kind, iters, lr in [("bias", 200, 0.05), ("ring", 300, 0.05), ("top", 300, 0.02), ("top+ring", 300, 0.02), ("gate(x)ring", 400, 0.05), ("top(x)ring", 400, 0.02)]:
    t0 = time.time()
    ptr, phe = feats(kind, tr, gate), feats(kind, he, gate)
    Wt = fit(ptr, ell_tr, y_tr, iters, lr)
    s = score(phe, ell_he, y_he, Wt, held_u)
    st = score(ptr, ell_tr, y_tr, Wt, np.arange(0))
    print(f"{kind:12s} right {s[0]:3d}/495  bits/digit at U {s[1]:.3f}  held bits/byte {s[2]:.3f}  train bits/byte {st[2]:.3f}  ({time.time() - t0:.0f} s)", flush=True)
