"""The founding at B against U's demand, as the pool law founds: a generalized eigenproblem, no start.

FOUND_AT_B_BY_U.py found that, placed in mode 41 and scored against U's tension, the crossing form
at B (chi_1(a0)'s read of the state times chi_1 of the arriving digit) takes share 1.69 of 2, where
the state at B alone takes 0.71: the criterion now puts the crossing first. Its gradient climbs
from blind starts stopped at 0.66. The founding law for a pool (the effective tension's pool fold)
needs no climb: the best face from a pool is the leading generalized eigenvector of the pool's
demand against its own loudness.

A pool here is every situated form at B with one class factor beta: c_B = beta_d (s^T a), a in
C^128, carried to U through mode 41 (c_U = lambda c_B + mu conj(c_B)). Its real part at U is
linear in (Re a, Im a): Re c_U = Phi theta, Phi of 256 real columns. The leading generalized
eigenvector of (Phi^T P_y Phi, Phi^T Phi), P_y the projection onto U's covectors, is the pool's
best single channel; its theta gives the complex form, read in both channels. Pools: the unit
(the state alone), each character chi_k (k = 1..5; its conjugate is the same pool), and the ten
characters together (the whole class-crossed lookup, 2,560 columns, where fitting in the sample
is read against the held-out read). Each found form is read held out at the acceptance cell B (the
495 held-out sums' B cells, an indicator fit of c0 on c_B's two channels at the training sums' B
cells). Uses FOUND_AT_B_BY_U.py's loading (argument 4) with its own arguments 1 to 3."""
import sys
src = open(sys.argv[4]).read()
exec(src[:src.index("cr = chi(1, C0b)")])

Qy = np.linalg.qr(y - y.mean(0))[0]

def pool_columns(beta):
    lb, mb = lam_ * beta[Db], mu_ * np.conj(beta[Db])
    return np.hstack([((lb + mb)[:, None] * Sb).real, ((lb - mb)[:, None] * (1j * Sb)).real])

def found(Phi):
    Phi = Phi - Phi.mean(0)
    A = (Qy.T @ Phi).T @ (Qy.T @ Phi)
    B = Phi.T @ Phi
    B = B + np.eye(len(B)) * 1e-9 * np.trace(B) / len(B)
    L = np.linalg.cholesky(B)
    w, V = np.linalg.eigh(np.linalg.solve(L, np.linalg.solve(L, A).T))
    th = np.linalg.solve(L.T, V[:, -1])
    return w[-1], th

def report(nm, beta):
    t1 = time.time()
    lead, th = found(pool_columns(beta))
    a = th[:128] + 1j * th[128:]
    describe(f"{nm}: leading single-channel share {lead:.4f}; the found form", a, beta, f" ({time.time() - t1:.1f} s)")

report("the unit (the state alone)", np.ones(10, dtype=complex))
for k in range(1, 6):
    report(f"chi_{k}", chi(k, np.arange(10)))
# the ten characters together: one pool of 2,560 columns
t1 = time.time()
cols = [pool_columns(chi(k, np.arange(10))) for k in range(10)]
lead, th = found(np.hstack(cols))
print(f"   the ten characters together: leading single-channel share {lead:.4f} in the sample ({time.time() - t1:.1f} s)", flush=True)
parts = [th[256 * k:256 * (k + 1)] for k in range(10)]
cb = sum((Sb @ (p[:128] + 1j * p[128:])) * chi(k, Db) for k, p in enumerate(parts))
ch = sum((Fh[SBh] @ (p[:128] + 1j * p[128:])) * chi(k, Dh[SBh]) for k, p in enumerate(parts))
X = np.stack([cb.real, cb.imag, np.ones(len(cb))], 1); s = np.abs(X[:, :2]).std(); X[:, :2] /= s
W = np.linalg.solve(X.T @ X + np.eye(3) * 1e-6, X.T @ np.eye(10)[C0b])
Xh = np.stack([ch.real / s, ch.imag / s, np.ones(len(ch))], 1)
pw = np.array([np.linalg.norm(p)**2 for p in parts]); pw /= pw.sum()
print(f"      its weight by character k=0..9: {' '.join(f'{x:.2f}' for x in pw)}; the form at B holds chi_1(c0) {held_frac_b(cb, chi(1, C0b)):.3f}; "
      f"held out, units at B {int((np.argmax(Xh @ W, 1) == C0h[SBh]).sum())} of {int(SBh.sum())}", flush=True)
print(f"done in {time.time() - t0:.1f} s")
