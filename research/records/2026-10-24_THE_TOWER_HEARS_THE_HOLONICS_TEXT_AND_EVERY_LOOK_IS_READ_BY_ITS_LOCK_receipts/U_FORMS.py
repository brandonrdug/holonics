"""The crossing at U at its own loudness, as a form of the state with itself.

U is the cell that codes a true sum's units digit. At the 8,986 training sums' U cells (eight parts,
each from rest, cells from 128): level 0's state before the class arriving at U (char/block{c}_ufull.txt,
released to /2^8 as at B) and the input covector there (char/block{c}_ucov.txt, /2^24). The region is
these cells (a label region, a ceiling), read against its own Y_r = sum y y^T, so its whole tension
is 64.

A form of the state with itself is c = (a^T s)(a'^T s), a and a' in C^128. With a' fixed it is
linear in a through u = s (a'^T s), centred over the region; it is scored by the founding's circular
criterion J = m^H Y_r^-1 m / sum |c|^2 and searched by alternating a and a' (generalized
eigenproblems). Starts: the outside reads of chi_1(a0) and chi_1(b0) at U (ridge, exterior), and two
blind starts from the region's principal pairs. Beside them: the outside product unsearched, the
exact crossing chi_1(c0) (a label), and the leading straight-line read of the state alone (no
crossing). Each form is read held out at the 495 sums' U cells (char/dev_ufull.txt) through an
indicator fit of c0 on its two channels (uncentred) at the training U cells."""
import importlib.util, math, sys, time
import numpy as np
t0 = time.time()
spec = importlib.util.spec_from_file_location("tm", "../../tools/tower_modes.py"); tm = importlib.util.module_from_spec(spec); spec.loader.exec_module(tm)
chi = lambda k, d: np.exp(2j * np.pi * k * np.asarray(d) / 10)

def states(text_path, full_path):
    text = open(text_path, "rb").read()
    role, info = tm.probe_roles(text)
    out = {}
    for i, _, _, lev in tm.parse(full_path, True):
        f = info[i + 1]
        assert f[0] == "+" and "U" in role[i + 1] and text[i + 1] - 48 == f[3]
        out[i] = (np.round(np.array([v for m in lev[0] for v in m[0:2]], dtype=float) / 2**8), f[1], f[2], f[3])
    return out, text

S_, Y_, A0, B0, C0, LN = [], [], [], [], [], []
for c in range(8):
    st, text = states(f"modes/block{c}.txt", f"char/block{c}_ufull.txt")
    lines = np.cumsum([0] + [1 if x == 10 else 0 for x in text])
    for line in open(f"char/block{c}_ucov.txt"):
        if not line.startswith("FORMS "):
            continue
        p = line.split(); i = int(p[1])
        s, a0, b0, c0 = st[i]
        S_.append(s); Y_.append(np.array([int(x) for x in p[3:]], dtype=float) / 2**24)
        A0.append(a0); B0.append(b0); C0.append(c0); LN.append(lines[i])
S_, Y_, A0, B0, C0, LN = map(np.array, (S_, Y_, A0, B0, C0, LN))
sth, _ = states("htext2/dev_arithmetic.txt", "char/dev_ufull.txt")
Sh = np.array([v[0] for v in sth.values()]); C0h = np.array([v[3] for v in sth.values()])
print(f"training sums' U cells {len(S_)}, held out {len(Sh)}; read in {time.time() - t0:.1f} s", flush=True)

y = Y_; Yi = np.linalg.inv(y.T @ y)
mu_s = S_.mean(0)

def geneig_top(A, B):
    B = B + np.eye(len(B)) * 1e-12 * np.trace(B).real / len(B)
    L = np.linalg.cholesky(B); Li = np.linalg.inv(L)
    w, U = np.linalg.eigh(Li @ A @ Li.conj().T)
    x = Li.conj().T @ U[:, -1]
    return w[-1], x / np.linalg.norm(x)

def share(cv):
    c = cv - cv.mean()
    C = np.stack([c.real, c.imag], 1)
    R, G = C.T @ y, C.T @ C
    return np.trace(Yi @ R.T @ np.linalg.pinv(G) @ R)

def J(cv):
    c = cv - cv.mean()
    m = y.T @ c
    return (m.conj() @ Yi @ m).real / (np.abs(c)**2).sum()

def step(a_fixed):
    r = S_ @ a_fixed
    U = S_ * r[:, None]
    U = U - U.mean(0)
    N = y.T @ U
    return geneig_top(N.conj().T @ Yi @ N, U.conj().T @ U)[1]

def search(a, a2, steps=200):
    j = J((S_ @ a) * (S_ @ a2))
    for _ in range(steps):
        a = step(a2); a2 = step(a)
        jn = J((S_ @ a) * (S_ @ a2))
        if jn - j <= 1e-9 * abs(j):
            j = jn; break
        j = jn
    return j, a, a2

def heldout(cv, cvh):
    X = np.stack([cv.real, cv.imag, np.ones(len(cv))], 1); s = np.abs(X[:, :2]).std(); X[:, :2] /= s
    W = np.linalg.solve(X.T @ X + np.eye(3) * 1e-6, X.T @ np.eye(10)[C0])
    Xh = np.stack([cvh.real / s, cvh.imag / s, np.ones(len(cvh))], 1)
    return int((np.argmax(Xh @ W, 1) == C0h).sum())

def held_frac(x, t):
    tr, te = LN % 2 == 0, LN % 2 == 1
    A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
    W = np.linalg.lstsq(A[tr], t[tr], rcond=None)[0]
    r = t[te] - A[te] @ W
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()

def describe(name, a, a2, j=None):
    cv, cvh = (S_ @ a) * (S_ @ a2), (Sh @ a) * (Sh @ a2)
    j = J(cv) if j is None else j
    print(f"   {name}: J {j:.4f}, share {share(cv):.4f}; the two reads hold chi_1(a0) {held_frac(S_ @ a, chi(1, A0)):.3f}/{held_frac(S_ @ a2, chi(1, A0)):.3f}, "
          f"chi_1(b0) {held_frac(S_ @ a, chi(1, B0)):.3f}/{held_frac(S_ @ a2, chi(1, B0)):.3f}; the form holds chi_1(c0) {held_frac(cv, chi(1, C0)):.3f}; "
          f"held out, units at U {heldout(cv, cvh)} of {len(Sh)}", flush=True)

def ridge_read(t):
    X = np.hstack([S_, np.ones((len(S_), 1))])
    w = np.linalg.solve(X.T @ X + np.eye(X.shape[1]) * 1e-6 * np.trace(X.T @ X) / X.shape[1], X.T @ t)
    return w[:-1]

# references
c_ex = chi(1, C0)
print(f"the exact crossing chi_1(c0) at the region's own loudness (a label): share {share(c_ex):.4f}, J {J(c_ex):.4f}", flush=True)
Sc = S_ - mu_s
jl, al = geneig_top(Sc.T @ y @ Yi @ y.T @ Sc, Sc.T @ Sc)
print(f"the leading straight-line read of the state alone: J {jl:.4f}", flush=True)
a_out, b_out = ridge_read(chi(1, A0)), ridge_read(chi(1, B0))
describe("the outside product, unsearched", a_out, b_out)
# searches
Cs = Sc.T @ Sc / len(Sc)
ev, E = np.linalg.eigh(Cs); E = E[:, ::-1]
starts = {"outside reads": (a_out, b_out), "principal 1+2 / 1+2": (E[:, 0] + 1j * E[:, 1], E[:, 0] + 1j * E[:, 1]),
          "principal 1+2 / 3+4": (E[:, 0] + 1j * E[:, 1], E[:, 2] + 1j * E[:, 3])}
for nm, (a, a2) in starts.items():
    t1 = time.time()
    j, a, a2 = search(a.astype(complex), a2.astype(complex))
    describe(f"searched from {nm} ({time.time() - t1:.1f} s)", a, a2, j)
print(f"done in {time.time() - t0:.1f} s")
