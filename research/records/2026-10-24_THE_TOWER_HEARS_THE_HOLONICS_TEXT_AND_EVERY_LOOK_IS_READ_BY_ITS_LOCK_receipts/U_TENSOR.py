"""The forms the tension at U asks for, read from its third moment.

A form of the state with itself, c = x^T W x (x the state at U whitened in the region), meets the
covector through m = sum over cells of y c. With the covector whitened in the region's own Y_r
(yw = (y - mean) L, L L^T = Y_r^-1, so the whole tension is 64), m_k = sum_ij W_ij T_ijk, where
T_ijk = sum over cells of yw_k x_i x_j is the tension's third moment against the state. The
founding's numerator for a form is this contraction; the alternating searches climbed it from
chosen starts. Here it is read whole: T unfolded as a (128*128) x 64 matrix and decomposed; its
leading left singular vectors are the quadratic forms W_1, W_2, ... the tension asks for most, in
order, with no start and no label. The singular values are set beside a foil: the same T with the
covectors permuted among the cells (the relation between state and tension removed, both marginals
kept), which gives the floor the spectral gap is read against.
Printed: the leading singular values and the foil's; for each leading form its single-channel share
and the character of c0 it holds most; the leading two forms as the two channels of one complex form
(share, J, the character of c0 held, the units at U held out); the leading 2, 4, 8, 16 forms together
held out; the leading form's eigenvalue spread (how few strands it needs); and what each of its
leading eigenvectors holds of a0's and b0's characters (one real channel holds at most half a
character). Labels only read what the decomposition found. Uses U_FORMS.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("# references")])

def best_char(x, d, nm):
    v = [(held_frac(x, chi(k, d)), k) for k in range(1, 6)]
    f, k = max(v)
    return f"chi_{k}({nm}) {f:.3f}"

Sc = S_ - mu_s
C = Sc.T @ Sc / len(Sc)
ev, E = np.linalg.eigh(C)
keep = ev > 1e-9 * ev.max()
ev, E = ev[keep][::-1], E[:, keep][:, ::-1]
Wh = E / np.sqrt(ev)
X, Xh = Sc @ Wh, (Sh - mu_s) @ Wh
dim = X.shape[1]
yc = y - y.mean(0)
L = np.linalg.cholesky(np.linalg.inv(yc.T @ yc))
yw = yc @ L

def third(yv):
    T = np.zeros((dim * dim, yv.shape[1]))
    for s0 in range(0, len(X), 500):
        xb = X[s0:s0 + 500]
        T += np.einsum("ni,nj->nij", xb, xb).reshape(len(xb), -1).T @ yv[s0:s0 + 500]
    return T

t1 = time.time()
T = third(yw)
U_, sv, _ = np.linalg.svd(T, full_matrices=False)
rng_perm = np.argsort((np.arange(len(yw)) * 7919) % len(yw))     # a fixed permutation (no RNG)
Tf = third(yw[rng_perm])
svf = np.linalg.svd(Tf, compute_uv=False)
print(f"whitened rank {dim}; third moment and its foil in {time.time() - t1:.1f} s", flush=True)
print("   singular values, leading 12: " + " ".join(f"{v:.3f}" for v in sv[:12]), flush=True)
print("   the foil's, leading 12:      " + " ".join(f"{v:.3f}" for v in svf[:12]), flush=True)

Ws = [U_[:, k].reshape(dim, dim) for k in range(16)]
Ws = [(W + W.T) / 2 for W in Ws]
cs = [((X @ W) * X).sum(1) for W in Ws]
chs = [((Xh @ W) * Xh).sum(1) for W in Ws]
for k in range(6):
    print(f"   form {k + 1}: share {share(cs[k].astype(complex)):.4f}; holds {best_char(cs[k].astype(complex), C0, 'c0')}", flush=True)
cv, cvh = cs[0] + 1j * cs[1], chs[0] + 1j * chs[1]
print(f"   forms 1 and 2 as one complex form: share {share(cv):.4f}, J {J(cv):.4f}; holds {best_char(cv, C0, 'c0')}; held out, units at U {heldout(cv, cvh)} of {len(Sh)}", flush=True)

def heldout_many(cvs, cvhs):
    Xt = np.stack(cvs, 1); sc = np.abs(Xt).std(0) + 1e-30
    Xg = np.stack(cvhs, 1)
    X1 = np.hstack([Xt / sc, np.ones((len(Xt), 1))]); X1h = np.hstack([Xg / sc, np.ones((len(Xg), 1))])
    W = np.linalg.solve(X1.T @ X1 + np.eye(X1.shape[1]) * 1e-6, X1.T @ np.eye(10)[C0])
    return int((np.argmax(X1h @ W, 1) == C0h).sum())

print("   held out, the leading forms together (real channels): " + "; ".join(f"{r}: {heldout_many(cs[:r], chs[:r])}" for r in (2, 4, 8, 16)) + f" of {len(Sh)}", flush=True)
for k in range(2):
    w, V = np.linalg.eigh(Ws[k])
    o = np.argsort(-np.abs(w))
    w, V = w[o], V[:, o]
    frac = np.cumsum(w**2) / (w**2).sum()
    print(f"   form {k + 1}'s eigenvalues, leading 8: " + " ".join(f"{v:+.3f}" for v in w[:8]) + f"; the leading 2, 4, 8 hold {frac[1]:.2f}, {frac[3]:.2f}, {frac[7]:.2f} of its square", flush=True)
    for r in range(4):
        z = (X @ V[:, r]).astype(complex)
        print(f"      eigenvector {r + 1}: holds {best_char(z, A0, 'a0')}, {best_char(z, B0, 'b0')}", flush=True)
print(f"done in {time.time() - t0:.1f} s")
