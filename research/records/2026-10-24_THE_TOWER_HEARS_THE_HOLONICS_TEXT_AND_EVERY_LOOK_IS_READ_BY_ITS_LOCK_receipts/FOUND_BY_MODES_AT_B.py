"""The founding at B against the demand the tower's own reverse sends to its modes.

FOUND_PLACE_AT_B.py founded the units crossing at B (471 of 495 held out) by scoring each form
placed in one mode against U's input covector carried back through that mode's own moves: U's
demand alone, the carry computed outside. The tower's reverse already carries every later face's
demand back through each mode's own moves: G_h, the covector of a level's modes after a cell's push
(read-tower-input-covectors with LEVEL 0, char/block{c}_dmode.txt, /2^24). A value placed in mode m
at the cell changes the code by Re(conj(G_m) delta h_m) to first order, so a form lifted into the
modes, h += V c with V real (128 x 2 on Re c, Im c), meets the tension G (128 real coordinates)
exactly as a form lifted into the input meets y.

So the founding is read here with G in y's place: a situated form c = (a^T s) beta_d (the state
before the arrival, s in R^128, a in C^128; the arriving digit d and its class factor beta), centred
within each arriving digit as the machine centres, against Y = sum G G^T (uncentred, the machine's
metric). The pool law founds a pool's best single channel with no start: the leading generalized
eigenvector of (Phi^T G Y^-1 G^T Phi, Phi^T Phi). Pools: the unit and the ring's characters chi_1 to
chi_5. Regions: the sums' B cells (the label region the exterior founding used) and every digit
arrival of the eight parts (no label). Beside it, the same founding against the input covector y.
Each found form is read held out at the acceptance cell B (an indicator fit of c0 on its two
channels at the training sums' B cells), with the placement its lift names: the modes holding most
of V's energy."""
import sys, math, importlib.util, time
import numpy as np
t0 = time.time()
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
DIG = 10
chi = lambda k, d: np.exp(2j * np.pi * k * np.asarray(d) / 10)

F, Yv, Gv, D, ROLE, OP, C0 = [], [], [], [], [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    role, info = tm.probe_roles(text)
    before = {}
    for i, _, _, lev in tm.parse(f"char/block{c}_dprev.txt", False):
        before[i + 1] = np.array([v for m in lev[0] for v in m], dtype=float)
    gm = {}
    for line in open(f"char/block{c}_dmode.txt"):
        if line.startswith("FORMS "):
            p = line.split(); gm[int(p[1])] = np.array([int(x) for x in p[3:]], dtype=float) / 2**24
    for line in open(f"char/block{c}_dcov.txt"):
        if not line.startswith("FORMS "):
            continue
        p = line.split(); i = int(p[1]); u = int(p[2])
        if not (48 <= u <= 57) or i not in before or i not in gm:
            raise SystemExit(f"block{c}: cell {i} is not a digit arrival with a state and a mode covector")
        F.append(np.round(before[i] / 2**8)); Yv.append(np.array([int(x) for x in p[3:]], dtype=float) / 2**24); Gv.append(gm[i])
        D.append(u - 48)
        r = role.get(i + 1, ()); f = info.get(i + 1)
        ROLE.append("B" in r); OP.append(f[0] if f else ""); C0.append(f[3] if f else -1)
F, Yv, Gv, D = np.array(F), np.array(Yv), np.array(Gv), np.array(D)
ROLE, OP, C0 = np.array(ROLE), np.array(OP), np.array(C0)
SB = ROLE & (OP == "+")
print(f"training digit arrivals {len(F)}, sums' B cells {SB.sum()}; mode covector width {Gv.shape[1]}, input covector width {Yv.shape[1]}; read in {time.time() - t0:.1f} s", flush=True)

text = open("htext2/dev_arithmetic.txt", "rb").read()
role, info = tm.probe_roles(text)
Fh, Dh, C0h, SBh = [], [], [], []
for i, _, _, lev in tm.parse("modes/dev_full_p7.txt", True):
    if not (48 <= text[i] <= 57):
        continue
    r = role.get(i + 1, ()); f = info.get(i + 1)
    Fh.append(np.round(np.array([v for m in lev[0] for v in m[:2]], dtype=float) / 2**8)); Dh.append(text[i] - 48)
    SBh.append("B" in r and f[0] == "+"); C0h.append(f[3] if f else -1)
Fh, Dh, C0h, SBh = np.array(Fh), np.array(Dh), np.array(C0h), np.array(SBh)
print(f"held-out sums' B cells {SBh.sum()}", flush=True)

def centred_within(x, d):
    out = x.copy()
    for k in range(DIG):
        q = d == k
        if q.any():
            out[q] -= x[q].mean(0)
    return out

def heldout_b(a, beta):
    cb = (F[SB] @ a) * beta[D[SB]]
    ch = (Fh[SBh] @ a) * beta[Dh[SBh]]
    X = np.stack([cb.real, cb.imag, np.ones(len(cb))], 1); s = np.abs(X[:, :2]).std(); X[:, :2] /= s
    W = np.linalg.solve(X.T @ X + np.eye(3) * 1e-6, X.T @ np.eye(10)[C0[SB]])
    Xh = np.stack([ch.real / s, ch.imag / s, np.ones(len(ch))], 1)
    return int((np.argmax(Xh @ W, 1) == C0h[SBh]).sum())

def holds_c0(a, beta):
    """How much of chi_1(c0) the form's value at the training sums' B cells holds (|corr|^2)."""
    c = (F[SB] @ a) * beta[D[SB]]; t = chi(1, C0[SB])
    c, t = c - c.mean(), t - t.mean()
    return abs(np.vdot(t, c))**2 / (np.vdot(c, c).real * np.vdot(t, t).real)

def found(region, target, beta):
    s, d, g = F[region], D[region], target[region]
    Y = g.T @ g; Yi = np.linalg.inv(Y)
    sc = centred_within(s, d)
    b = beta[d]
    Phi = np.hstack([b.real[:, None] * sc, -b.imag[:, None] * sc])
    Gp = g.T @ Phi
    A = Gp.T @ Yi @ Gp
    B = Phi.T @ Phi
    B = B + np.eye(len(B)) * 1e-9 * np.trace(B) / len(B)
    L = np.linalg.cholesky(B)
    w, V = np.linalg.eigh(np.linalg.solve(L, np.linalg.solve(L, A).T))
    th = np.linalg.solve(L.T, V[:, -1])
    a = th[:128] + 1j * th[128:]
    c = (sc @ a) * b
    C = np.stack([c.real, c.imag], 1)
    R, Gc = C.T @ g, C.T @ C
    share2 = np.trace(Yi @ R.T @ np.linalg.pinv(Gc) @ R)
    lift = Yi @ R.T @ np.linalg.pinv(Gc)            # the fitted lift of (Re c, Im c), one row per tension coordinate
    return w[-1], w[-2], share2, a, lift

def placement(lift):
    e = (lift**2).sum(1)
    per_mode = e[0::2] + e[1::2]
    top = np.argsort(per_mode)[::-1][:3]
    return ", ".join(f"mode {m} {per_mode[m] / per_mode.sum():.2f}" for m in top)

pools = [("the unit", np.ones(10, dtype=complex))] + [(f"chi_{k}", chi(k, np.arange(10))) for k in range(1, 6)]
for rname, region in [("the sums' B cells", SB), ("every digit arrival", np.ones(len(F), dtype=bool))]:
    for tname, target in [("the modes' covector G", Gv), ("the input covector y", Yv)]:
        t1 = time.time()
        print(f"{rname}, against {tname}:", flush=True)
        for pname, beta in pools:
            lead, second, share2, a, lift = found(region, target, beta)
            where = f"; placed in {placement(lift)}" if target is Gv else ""
            print(f"   {pname}: leading single-channel share {lead:.4f} (second {second:.4f}); its form's two channels {share2:.4f}; holds chi_1(c0) at B {holds_c0(a, beta):.3f}; held out, units at B {heldout_b(a, beta)} of {int(SBh.sum())}{where}", flush=True)
        print(f"   ({time.time() - t1:.1f} s)", flush=True)
print(f"done in {time.time() - t0:.1f} s")
