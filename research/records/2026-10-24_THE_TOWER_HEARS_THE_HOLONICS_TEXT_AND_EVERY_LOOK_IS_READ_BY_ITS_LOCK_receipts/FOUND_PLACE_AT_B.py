"""Which placement and which class factor would the founding at B choose, with no label?

FOUND_POOL_AT_B.py founded the chi_1 pool at B against U's demand carried through mode 41, with no
start, and its form read the units at B in 444 of 495 held-out sums. Mode 41 was chosen by a
reading that placed the exact crossing (a label). Here the founding chooses both: for every mode m
of level 0 as the placement (the form's value carried from B to U through that mode's own moves)
and every pool (the unit, the characters chi_1 .. chi_5 of the ring), the pool's leading single-
channel share of U's tension is read by the same generalized eigenproblem. The pairs are ranked by
that share alone. Printed: each pool's best placement; the ten leading pairs; and the leading
pair's found form, read held out at the acceptance cell B (an indicator fit of c0 on its two
channels at the training sums' B cells), beside each pool's best form held out.
Uses REGION_SHARE.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])
NM = 64

# each digit arrival's (part, cell), in REGION_SHARE's order
cells = []
for c in range(8):
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            cells.append((c, int(line.split()[1])))
# per part: the sums' pb -> pu, U's covectors, the moves of the chosen mode
rows, Yu, lam_, mu_ = [], [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    pu_of, start = {}, 0
    for line in text.split(b"\n"):
        m_ = tm.tower_circuit.EQ.match(line)
        if m_:
            a_, op_, b_, cc_ = m_.groups()
            pu_of[start + len(a_) + len(b_)] = start + len(line) - 1
        start += len(line) + 1
    ucov = {}
    for line in open(f"char/block{c}_ucov.txt"):
        if line.startswith("FORMS "):
            p = line.split(); ucov[int(p[1])] = np.array([int(x) for x in p[3:]], dtype=float) / 2**24
    mv = {}
    for i, _, _, lev in tm.parse(f"char/block{c}_bufull.txt", True):
        md = np.array(lev[0], dtype=float)
        mv[i] = ((md[:, 6] + 1j * md[:, 7]) / 2**30, (md[:, 8] + 1j * md[:, 9]) / 2**30)
    for k, (cc, i) in enumerate(cells):
        if cc != c or not SB[k]:
            continue
        pu = pu_of[i]
        if pu - 1 not in ucov:
            continue
        h1, hi = np.ones(NM, dtype=complex), np.full(NM, 1j)
        for j in range(i + 1, pu):
            l, b = mv[j]
            h1, hi = l * h1 + b * np.conj(h1), l * hi + b * np.conj(hi)
        rows.append(k); Yu.append(ucov[pu - 1]); lam_.append((h1 - 1j * hi) / 2); mu_.append((h1 + 1j * hi) / 2)
rows, Yu, lam_, mu_ = np.array(rows), np.array(Yu), np.array(lam_), np.array(mu_)
Sb, Db, C0b, A0b = F[rows], D[rows], C0[rows], A0[rows]
print(f"sums with B, U and the carry {len(rows)}, every mode's carry; read in {time.time() - t0:.1f} s", flush=True)
LAM, MU = lam_, mu_                     # n x 64

y = Yu; Yi = np.linalg.inv(y.T @ y)
def share2(cv):
    c = cv - cv.mean()
    C = np.stack([c.real, c.imag], 1)
    R, G = C.T @ y, C.T @ C
    Gi = np.linalg.pinv(G)
    return np.trace(Yi @ R.T @ Gi @ R), C, R, Gi

def carried(r, beta):
    cb = r * beta[Db]
    return lam_ * cb + mu_ * np.conj(cb), cb

def score_and_grad(a, beta):
    r = Sb @ a
    cu, cb = carried(r, beta)
    s, C, R, Gi = share2(cu)
    Dm = 2 * (y @ Yi @ R.T @ Gi - C @ Gi @ R @ Yi @ R.T @ Gi)
    g = Dm[:, 0] + 1j * Dm[:, 1]; g -= g.mean()
    w = np.conj(g) * lam_ + g * np.conj(mu_)            # d share = Re sum w * (dc_B)
    ga = np.conj(Sb.T @ (w * beta[Db]))
    gb = np.conj(np.array([(w * r)[Db == q].sum() for q in range(DIG)]))
    return s, ga, gb

def climb(a, beta, steps):
    a = a / np.linalg.norm(a); beta = beta / np.linalg.norm(beta)
    s, ga, gb = score_and_grad(a, beta)
    st = 1.0
    for t in range(steps):
        while True:
            an, bn = a + st * ga / (np.linalg.norm(ga) + 1e-30), beta + st * gb / (np.linalg.norm(gb) + 1e-30)
            an /= np.linalg.norm(an); bn /= np.linalg.norm(bn)
            sn, gan, gbn = score_and_grad(an, bn)
            if sn > s or st < 1e-9:
                break
            st /= 2
        if sn - s <= 1e-9 * abs(s):
            return sn, an, bn, t
        a, beta, s, ga, gb = an, bn, sn, gan, gbn
        st *= 1.5
    return s, a, beta, steps

def held_frac_b(x, t):
    ln = LNb
    tr, te = (ln % 2 == 0), (ln % 2 == 1)
    A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
    W = np.linalg.lstsq(A[tr], t[tr], rcond=None)[0]
    r = t[te] - A[te] @ W
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()

LNb = []
for k in rows:
    c, i = cells[k]
    LNb.append(i)              # placeholder replaced below by line numbers
lines_of = {}
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    lines_of[c] = np.cumsum([0] + [1 if x == 10 else 0 for x in text])
LNb = np.array([lines_of[cells[k][0]][cells[k][1]] for k in rows])

def heldout_b(a, beta):
    cb = (Sb @ a) * beta[Db]
    ch = (Fh[SBh] @ a) * beta[Dh[SBh]]
    X = np.stack([cb.real, cb.imag, np.ones(len(cb))], 1); s = np.abs(X[:, :2]).std(); X[:, :2] /= s
    W = np.linalg.solve(X.T @ X + np.eye(3) * 1e-6, X.T @ np.eye(10)[C0b])
    Xh = np.stack([ch.real / s, ch.imag / s, np.ones(len(ch))], 1)
    return int((np.argmax(Xh @ W, 1) == C0h[SBh]).sum())

def describe(nm, a, beta, extra=""):
    cu, cb = carried(Sb @ a, beta)
    p1 = abs(chi(1, np.arange(10)).conj() @ beta)**2 / (10 * np.linalg.norm(beta)**2)
    p9 = abs(chi(9, np.arange(10)).conj() @ beta)**2 / (10 * np.linalg.norm(beta)**2)
    print(f"   {nm}{extra}: share of U's tension {share2(cu)[0]:.4f}; the state read holds chi_1(a0) {held_frac_b(Sb @ a, chi(1, A0b)):.3f}; "
          f"beta on k=1 {p1:.2f}, k=9 {p9:.2f}; the form at B holds chi_1(c0) {held_frac_b(cb, chi(1, C0b)):.3f}; "
          f"held out, units at B {heldout_b(a, beta)} of {int(SBh.sum())}", flush=True)


Qy = np.linalg.qr(y - y.mean(0))[0]

def pool_columns(beta, lam, mu):
    lb, mb = lam * beta[Db], mu * np.conj(beta[Db])
    return np.hstack([((lb + mb)[:, None] * Sb).real, ((lb - mb)[:, None] * (1j * Sb)).real])

def found(Phi):
    Phi = Phi - Phi.mean(0)
    A = (Qy.T @ Phi).T @ (Qy.T @ Phi)
    B = Phi.T @ Phi
    B = B + np.eye(len(B)) * 1e-9 * np.trace(B) / len(B)
    L = np.linalg.cholesky(B)
    w, V = np.linalg.eigh(np.linalg.solve(L, np.linalg.solve(L, A).T))
    return w[-1], np.linalg.solve(L.T, V[:, -1])

pools = {"the unit": np.ones(10, dtype=complex)}
pools.update({f"chi_{k}": chi(k, np.arange(10)) for k in range(1, 6)})
t1 = time.time()
res = []
for m in range(NM):
    for nm, beta in pools.items():
        lead, th = found(pool_columns(beta, LAM[:, m], MU[:, m]))
        res.append((lead, nm, m, th))
print(f"{len(res)} pairs founded in {time.time() - t1:.1f} s", flush=True)
res.sort(key=lambda r: -r[0])

def describe_b(nm, m, th):
    beta = pools[nm]; a = th[:128] + 1j * th[128:]
    lam_[:], mu_[:] = LAM[:, m], MU[:, m]
    describe(f"{nm} placed in mode {m}", a, beta)

lam_, mu_ = LAM[:, 0].copy(), MU[:, 0].copy()
print("each pool's best placement: " + "; ".join(f"{nm} mode {next(r[2] for r in res if r[1] == nm)} ({next(r[0] for r in res if r[1] == nm):.4f})" for nm in pools), flush=True)
print("the ten leading pairs: " + "; ".join(f"{r[1]} in mode {r[2]} {r[0]:.4f}" for r in res[:10]), flush=True)
for nm in pools:
    r = next(r for r in res if r[1] == nm)
    describe_b(nm, r[2], r[3])
print(f"done in {time.time() - t0:.1f} s")
