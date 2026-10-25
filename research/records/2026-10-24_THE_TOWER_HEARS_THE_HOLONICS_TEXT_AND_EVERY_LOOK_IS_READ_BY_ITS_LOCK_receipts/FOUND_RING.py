"""The founding of a placed form with its reader: the form's ring.

CROSSING_DEMAND.py located why the tower's own mode covector does not found the units crossing at
B: the readers at U read the units through modes 4, 15, 2, 6 and 14 (0.42 to 0.52 of the crossing's
two channels each), the slow modes that carry a value from B to U alike for both lengths (41, 56,
48) hardly at all (0.08 for 41). A value placed in a node mode reaches U whole and finds no reader
there. So the founding founds the placed form together with its reader.

The form's ring: a situated form c_t = (a^T s_t) beta_(d_t) (the state before the arrival, the
arriving digit's class factor; zero where no digit arrives) is pushed into a ring that rides one
placement mode m's own moves, r_t = lambda_(m,t) r_(t-1) + beta_(m,t) conj(r_(t-1)) + c_t, and the
ring is read at every cell through a lift into the input, x0_t += P (Re r_t, Im r_t). With no memory
(lambda = beta = 0) this is the machine's present situated lift. The founding's criterion is the
machine's: the circular share ||sum_t Re(r_t) y_t||^2_(Y^-1) + ||sum_t Im(r_t) y_t||^2_(Y^-1) over
sum_t |r_t|^2 (y_t the input covector at every cell, Y = sum y y^T, r centred within the arriving
class at the reading cell), whose leading generalized eigenvector over a in C^128 founds each
(placement, pool) with no start; then its exact two-channel share tr(Y^-1 R^T G^-1 R).

The region is no label: every digit arrival of the eight training parts pushes, every cell from 128
reads (char/block{c}_allmoves.i32 and _allcov.i32, read-tower-modes and read-tower-input-covectors at
every cell). Each found form is read held out at the acceptance cell B as before. Arguments: the
placement modes (comma separated; -1 is no memory) and the pools (unit, chi1 ... chi5)."""
import sys, importlib.util, time
import numpy as np
t0 = time.time()
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
chi = lambda k, d: np.exp(2j * np.pi * k * np.asarray(d) / 10)
MODES = [int(x) for x in sys.argv[1].split(",")]
POOLS = sys.argv[2].split(",")

parts = []
F_SB, D_SB, C0_SB = [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    role, info = tm.probe_roles(text)
    mv = np.fromfile(f"char/block{c}_allmoves.i32", dtype=np.int32).reshape(-1, 2 + 256)
    cv = np.fromfile(f"char/block{c}_allcov.i32", dtype=np.int32).reshape(-1, 2 + 64)
    if not (np.array_equal(mv[:, 0], cv[:, 0]) and np.array_equal(mv[:, 0], np.arange(128, len(text) - 1))):
        raise SystemExit(f"block{c}: the moves and covectors are not every cell")
    lam = (mv[:, 2::4] + 1j * mv[:, 3::4]) / 2**30
    bet = (mv[:, 4::4] + 1j * mv[:, 5::4]) / 2**30
    y = cv[:, 2:].astype(float) / 2**24
    cls = cv[:, 1]
    S = np.zeros((len(cls), 128))
    has = np.zeros(len(cls), dtype=bool)
    for i, _, _, lev in tm.parse(f"char/block{c}_dprev.txt", False):
        j = i + 1 - 128
        if 0 <= j < len(cls) and 48 <= cls[j] <= 57:
            S[j] = np.round(np.array([v for m in lev[0] for v in m], dtype=float) / 2**8); has[j] = True
    dig = (cls >= 48) & (cls <= 57)
    if (dig & ~has).any():
        raise SystemExit(f"block{c}: a digit arrival without its state")
    for j in np.nonzero(dig)[0]:
        i = j + 128
        r = role.get(i + 1, ()); f = info.get(i + 1)
        if "B" in r and f and f[0] == "+":
            F_SB.append(S[j]); D_SB.append(cls[j] - 48); C0_SB.append(f[3])
    parts.append((lam, bet, y, cls, S, dig))
F_SB, D_SB, C0_SB = np.array(F_SB), np.array(D_SB), np.array(C0_SB)
cls_all = np.concatenate([p[3] for p in parts]); y_all = np.concatenate([p[2] for p in parts])
Y = y_all.T @ y_all; Yi = np.linalg.inv(Y)
N = len(cls_all)
print(f"cells {N}, digit arrivals {int(sum(p[5].sum() for p in parts))}, sums' B cells {len(C0_SB)}; read in {time.time() - t0:.1f} s", flush=True)

text = open("htext2/dev_arithmetic.txt", "rb").read()
role, info = tm.probe_roles(text)
Fh, Dh, C0h = [], [], []
for i, _, _, lev in tm.parse("modes/dev_full_p7.txt", True):
    if not (48 <= text[i] <= 57):
        continue
    r = role.get(i + 1, ()); f = info.get(i + 1)
    if "B" in r and f[0] == "+":
        Fh.append(np.round(np.array([v for m in lev[0] for v in m[:2]], dtype=float) / 2**8)); Dh.append(text[i] - 48); C0h.append(f[3])
Fh, Dh, C0h = np.array(Fh), np.array(Dh), np.array(C0h)

def heldout_b(a, beta):
    cb = (F_SB @ a) * beta[D_SB]
    ch = (Fh @ a) * beta[Dh]
    X = np.stack([cb.real, cb.imag, np.ones(len(cb))], 1); s = np.abs(X[:, :2]).std(); X[:, :2] /= s
    W = np.linalg.solve(X.T @ X + np.eye(3) * 1e-6, X.T @ np.eye(10)[C0_SB])
    Xh = np.stack([ch.real / s, ch.imag / s, np.ones(len(ch))], 1)
    return int((np.argmax(Xh @ W, 1) == C0h).sum())

def holds_c0(a, beta):
    c = (F_SB @ a) * beta[D_SB]; t = chi(1, C0_SB)
    c, t = c - c.mean(), t - t.mean()
    return abs(np.vdot(t, c))**2 / (np.vdot(c, c).real * np.vdot(t, t).real)

def ring_columns(m, beta):
    """Phi (N x 2 x 256): Re r_t and Im r_t as linear functions of theta = (Re a, Im a)."""
    out = []
    for lam, bet, y, cls, S, dig in parts:
        n = len(cls)
        P = np.zeros((n, 2, 256))
        b = np.zeros(n, dtype=complex); b[dig] = beta[cls[dig] - 48]
        Cr = np.concatenate([b.real[:, None] * S, -b.imag[:, None] * S], 1)
        Ci = np.concatenate([b.imag[:, None] * S, b.real[:, None] * S], 1)
        if m < 0:
            P[:, 0], P[:, 1] = Cr, Ci
        else:
            l, q = lam[:, m], bet[:, m]
            M = np.stack([np.stack([l.real + q.real, q.imag - l.imag], 1), np.stack([l.imag + q.imag, l.real - q.real], 1)], 1)
            cur = np.zeros((2, 256))
            for t in range(n):
                cur = M[t] @ cur
                cur[0] += Cr[t]; cur[1] += Ci[t]
                P[t] = cur
        out.append(P)
    P = np.concatenate(out)
    for u in np.unique(cls_all):
        q = cls_all == u
        P[q] -= P[q].mean(0)
    return P

def found(P):
    X0, X1 = y_all.T @ P[:, 0], y_all.T @ P[:, 1]
    A = X0.T @ Yi @ X0 + X1.T @ Yi @ X1
    Q = P[:, 0].T @ P[:, 0] + P[:, 1].T @ P[:, 1]
    Q = Q + np.eye(256) * 1e-9 * np.trace(Q) / 256
    L = np.linalg.cholesky(Q)
    w, V = np.linalg.eigh(np.linalg.solve(L, np.linalg.solve(L, A).T))
    th = np.linalg.solve(L.T, V[:, -1])
    C = np.stack([P[:, 0] @ th, P[:, 1] @ th], 1)
    R, G = C.T @ y_all, C.T @ C
    share2 = np.trace(Yi @ R.T @ np.linalg.pinv(G) @ R)
    return w[-1], share2, th[:128] + 1j * th[128:]

for pool in POOLS:
    beta = np.ones(10, dtype=complex) if pool == "unit" else chi(int(pool[3:]), np.arange(10))
    for m in MODES:
        t1 = time.time()
        lead, share2, a = found(ring_columns(m, beta))
        where = "no memory" if m < 0 else f"mode {m}"
        print(f"   {pool} placed in {where}: circular share {lead:.4f}, exact two channels {share2:.4f}; holds chi_1(c0) at B {holds_c0(a, beta):.3f}; held out, units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t1:.1f} s)", flush=True)
print(f"done in {time.time() - t0:.1f} s")
