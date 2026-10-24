"""Read in a region's own tension, is the sum's units crossing the leading form of the region the
lock marks? An exterior reading on the digit arrivals of the training equation block (eight parts,
each from rest, cells from 128): level 0's state before the digit arrives (the modes after the
previous cell, char/block{c}_dprev.txt, released to the face's grain, /2^8) and the covector the
tower's reverse sends to the cell's input (char/block{c}_dcov.txt, /2^24).

A region r is a set of these cells. Its own tension is Y_r = sum over r of y y^T (uncentred, as the
founding's Y). A complex form of the state and the arriving digit, c = (a^T s)(beta_d), centred
within each digit inside r, is scored by the founding's circular criterion in r's own unit,
J_r = m^H Y_r^-1 m / sum |c|^2, m = sum c y, and reported as its two channels' exact canonical share
s_r = tr(G^-1 R Y_r^-1 R^T) (at most 2 for one form). The best such form in r is searched by
alternating a (in C^128) and beta (in C^10), from the unit, the ring and the outside form
(char/ideal_quiet.txt) starts. Beside it: the outside form itself, the exact crossing chi_1(c0) on
the sums' B cells, and the largest squared canonical correlation of the whole class-crossed lookup
(a separate read of the state per digit), the ceiling of any form in r.

The found form is then read on the held-out equations (modes/dev_full_p7.txt, the before-state at
every cell) at the sums' B cells, through a straight-line indicator fit of c0 on its two channels
fitted at the training sums' B cells: how many of the 495 held-out sums' units it reads.

Regions: every digit arrival; the label region (the sums' B cells alone, a ceiling with a label);
and the sectors (16) of the relative phase of the mode pairs the lock reading named, 42-35 and
57-35. Their choice used the held-out label; whether the criterion itself picks them is a separate
reading."""
import sys, math, importlib.util, time
import numpy as np
t0 = time.time()
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
DIG = 10
chi = lambda k, d: np.exp(2j * np.pi * k * np.asarray(d) / 10)

# ---- training digit arrivals
F, Yv, D, ROLE, OP, A0, B0, C0 = [], [], [], [], [], [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    role, info = tm.probe_roles(text)
    before = {}
    for i, _, _, lev in tm.parse(f"char/block{c}_dprev.txt", False):
        before[i + 1] = np.array([v for m in lev[0] for v in m], dtype=float)
    for line in open(f"char/block{c}_dcov.txt"):
        if not line.startswith("FORMS "):
            continue
        p = line.split(); i = int(p[1]); u = int(p[2])
        if not (48 <= u <= 57) or i not in before:
            raise SystemExit(f"block{c}: cell {i} is not a digit arrival with a state")
        F.append(np.round(before[i] / 2**8)); Yv.append(np.array([int(x) for x in p[3:]], dtype=float) / 2**24)
        D.append(u - 48)
        r = role.get(i + 1, ()); f = info.get(i + 1)
        ROLE.append("B" in r); OP.append(f[0] if f else ""); A0.append(f[1] if f else -1); B0.append(f[2] if f else -1); C0.append(f[3] if f else -1)
F, Yv, D = np.array(F), np.array(Yv), np.array(D)
ROLE, OP, A0, B0, C0 = np.array(ROLE), np.array(OP), np.array(A0), np.array(B0), np.array(C0)
SB = ROLE & (OP == "+")
print(f"training digit arrivals {len(F)}; second operands' units (B) {ROLE.sum()}, of them sums {SB.sum()}; read in {time.time()-t0:.1f} s")
H = F[:, 0::2] + 1j * F[:, 1::2]   # the 64 modes, complex

# ---- held-out: before-state at the sums' B cells
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
Hh = Fh[:, 0::2] + 1j * Fh[:, 1::2]
print(f"held-out digit arrivals {len(Fh)}, sums' B cells {SBh.sum()}")

# ---- the outside form
line = open("char/ideal_quiet.txt").read().split("\n")[1]
fld = {k: v for k, v in (f.split("=", 1) for f in line.split()[2:])}
a_ideal = np.array([int(x) for x in fld["a"].split(",")], dtype=float) + 1j * np.array([int(x) for x in fld["ai"].split(",")], dtype=float)
a_ideal /= np.linalg.norm(a_ideal)
beta_ideal = chi(1, np.arange(10))

def geneig_top(A, B):
    """The top generalized eigenpair of Hermitian A against positive definite B."""
    B = B + np.eye(len(B)) * 1e-12 * np.trace(B).real / len(B)
    L = np.linalg.cholesky(B)
    Li = np.linalg.inv(L)
    w, U = np.linalg.eigh(Li @ A @ Li.conj().T)
    x = Li.conj().T @ U[:, -1]
    return w[-1], x / np.linalg.norm(x)

class Region:
    def __init__(self, m):
        self.m = m; self.n = int(m.sum())
        f, y, d = F[m], Yv[m], D[m]
        self.Y = y.T @ y; self.Yi = np.linalg.inv(self.Y)
        self.M, self.S, self.mean = [], [], []
        for k in range(DIG):
            q = d == k
            mu = f[q].mean(0) if q.any() else np.zeros(F.shape[1])
            fc = f[q] - mu
            self.M.append(fc.T @ y[q]); self.S.append(fc.T @ fc); self.mean.append(mu)
        self.M, self.S, self.mean = np.array(self.M), np.array(self.S), np.array(self.mean)
        self.fc = f - self.mean[d]; self.y = y; self.d = d
    def J(self, a, beta):
        m = np.einsum("k,kpq,p->q", beta, self.M, a)
        den = sum(abs(beta[k])**2 * (a.conj() @ self.S[k] @ a).real for k in range(DIG))
        return (m.conj() @ self.Yi @ m).real / den
    def share(self, a, beta):
        c = (self.fc @ a) * beta[self.d]
        C = np.stack([c.real, c.imag], 1)
        R, G = C.T @ self.y, C.T @ C
        return np.trace(self.Yi @ R.T @ np.linalg.solve(G, R))
    def search(self, a, beta, steps=300):
        j = self.J(a, beta)
        for _ in range(steps):
            V = np.einsum("kpq,p->qk", self.M, a)
            p = np.array([(a.conj() @ self.S[k] @ a).real for k in range(DIG)])
            _, beta = geneig_top(V.conj().T @ self.Yi @ V, np.diag(p))
            N = np.einsum("k,kpq->qp", beta, self.M)
            _, a = geneig_top(N.conj().T @ self.Yi @ N, np.einsum("k,kpq->pq", np.abs(beta)**2, self.S).astype(complex))
            jn = self.J(a, beta)
            if jn - j <= 1e-10 * abs(j):
                j = jn; break
            j = jn
        return j, a, beta
    def ceiling(self):
        K = sum(self.M[k].T @ np.linalg.solve(self.S[k] + np.eye(len(self.S[k])) * 1e-9 * np.trace(self.S[k]), self.M[k]) for k in range(DIG) if np.trace(self.S[k]) > 0)
        w = np.linalg.eigvals(self.Yi @ K).real
        return np.sort(w)[::-1]
    def starts(self):
        A = np.einsum("kpq,qr,ksr->ps", self.M, self.Yi, self.M)
        B = self.S.sum(0)
        L = np.linalg.cholesky(B + np.eye(len(B)) * 1e-12 * np.trace(B)); Li = np.linalg.inv(L)
        w, U = np.linalg.eigh(Li @ A @ Li.T)
        e1, e2 = Li.T @ U[:, -1], Li.T @ U[:, -2]
        ones = np.ones(DIG, dtype=complex)
        return {"unit": (e1.astype(complex), ones), "ring": (e1 + 1j * e2, ones), "outside": (a_ideal.copy(), beta_ideal.copy())}

def read_heldout(a, beta, reg, hm):
    """c0 at the held-out sums' B cells from the form's two channels as the machine reads them
    (uncentred, c = (a^T s) beta_d), an indicator fit at the training sums' B cells of the region;
    a held-out cell outside the region (hm false) receives nothing from the form."""
    tr = SB & reg.m
    ct = (F[tr] @ a) * beta[D[tr]]
    ch = (Fh[SBh] @ a) * beta[Dh[SBh]] * hm[SBh]
    X = np.stack([ct.real, ct.imag, np.ones(len(ct))], 1); s = np.abs(X[:, :2]).std()
    X[:, :2] /= s
    W = np.linalg.solve(X.T @ X + np.eye(3) * 1e-6, X.T @ np.eye(10)[C0[tr]])
    Xh = np.stack([ch.real / s, ch.imag / s, np.ones(len(ch))], 1)
    return int((np.argmax(Xh @ W, 1) == C0h[SBh]).sum())

def character_of(beta):
    """Alignment of beta with the characters of the ring of ten, |sum beta_d conj chi_k(d)| / (sqrt(10)|beta|)."""
    return [abs(beta @ chi(k, np.arange(10)).conj()) / (math.sqrt(10) * np.linalg.norm(beta)) for k in range(10)]

def report(name, m, hm, full=True):
    reg = Region(m)
    sb = int((SB & m).sum())
    out = f"{name}: cells {reg.n}, sums' B cells {sb} ({sb / SB.sum():.2f} of them, {sb / max(reg.n,1):.2f} of the region)"
    best = None
    for sname, (a, b) in reg.starts().items():
        j, a2, b2 = reg.search(a, b)
        if best is None or j > best[0]:
            best = (j, a2, b2, sname)
        out += f"\n   from {sname}: J {j:.4f}"
    j, a, b, sname = best
    ch = character_of(b)
    k = int(np.argmax(ch[1:])) + 1
    out += f"\n   best ({sname}): share {reg.share(a, b):.4f}; beta's nearest character k={k} ({ch[k]:.2f}; k=0 {ch[0]:.2f}); held out, sums' units at B {read_heldout(a, b, reg, hm)} of {SBh.sum()}"
    out += f"\n   the outside form unsearched: share {reg.share(a_ideal, beta_ideal):.4f}, J {reg.J(a_ideal, beta_ideal):.4f}; held out {read_heldout(a_ideal, beta_ideal, reg, hm)}"
    if sb:
        ex = np.where(SB[m], chi(1, np.where(SB[m], C0[m], 0)), 0)
        C = np.stack([ex.real, ex.imag], 1)
        Cc = C.copy()
        for kk in range(DIG):
            q = reg.d == kk; Cc[q] -= C[q].mean(0)
        R, G = Cc.T @ reg.y, Cc.T @ Cc
        out += f"\n   the exact crossing chi_1(c0) on the region's sums' B cells (a label): share {np.trace(reg.Yi @ R.T @ np.linalg.solve(G, R)):.4f}"
    if full:
        w = reg.ceiling()
        out += f"\n   the class-crossed lookup's squared canonical correlations (ceiling of any form): {', '.join(f'{x:.3f}' for x in w[:6])}"
    print(out, flush=True)
    return best

report("every digit arrival", np.ones(len(F), bool), np.ones(len(Fh), bool))
report("the sums' B cells (label region)", SB, SBh)
for j, k in ((42, 35), (57, 35)):
    sec = np.floor((np.angle(H[:, j] * np.conj(H[:, k])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
    sech = np.floor((np.angle(Hh[:, j] * np.conj(Hh[:, k])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
    order = sorted(range(16), key=lambda s: -(SB & (sec == s)).sum())
    print(f"lock modes {j}-{k}: sectors by their sums' B cells: " + ", ".join(f"{s}:{(SB & (sec == s)).sum()}/{(sec == s).sum()}" for s in order[:6]))
    for s in order[:2]:
        print(f"   held out, sector {s} holds {(SBh & (sech == s)).sum()} of the {SBh.sum()} sums' B cells")
        report(f"lock {j}-{k} sector {s}", sec == s, sech == s)
print(f"done in {time.time()-t0:.1f} s")
