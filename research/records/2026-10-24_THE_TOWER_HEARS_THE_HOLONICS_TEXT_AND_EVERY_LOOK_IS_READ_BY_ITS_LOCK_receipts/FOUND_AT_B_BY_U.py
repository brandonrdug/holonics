"""Founding at B against the demand at U, through the mode that carries B to U the same way.

CARRY_B_TO_U.py found mode 41 of level 0 carrying a value placed at B to U alike for both result
lengths: the exact crossing chi_1(c0) placed there reaches U holding 0.90 of itself, with share 1.74
of U's own tension. A form placed at B in that mode is demanded by U's tension, not by the
covector that reaches B through every path (where the crossing's demand cancels to 0.39).

So the founding is read here at B with U's demand: a situated form at B, c_B = (a^T s_B) beta_d (the
state before the arrival at B, s_B in R^128, a in C^128; the arriving digit d = b0 and its class
factor beta in C^10), is carried to U through mode 41's own moves of that sum,
c_U = lambda c_B + mu conj(c_B) (the carries of 1 and i give lambda and mu), and scored by its
two-channel share of U's tension (U's input covectors, Y_r over the sums' U cells). The form is
searched by gradient ascent on that share from four starts:
- blind: the whitened principal pair 1+2 of the B states, with beta the ring's first character
  (the coupling's first mode found without labels, CLASS_MODES.py) and with beta the unit;
- outside: the read of chi_1(a0) at B (char/ideal_quiet.txt) with beta = chi_1, and that read
  unsearched.
Beside them, the competitor any founding must beat: the share of U's tension that a straight-line
read of the B state alone can take in two channels (its top two canonical correlations squared).
Each form is read held out at the acceptance cell B: the 495 held-out sums' B cells, through an
indicator fit of c0 on c_B's two channels (uncentred) at the training sums' B cells. Uses
REGION_SHARE.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])
MODE, STEPS = int(sys.argv[2]), int(sys.argv[3])

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
        md = lev[0][MODE]
        mv[i] = ((md[6] + 1j * md[7]) / 2**30, (md[8] + 1j * md[9]) / 2**30)
    for k, (cc, i) in enumerate(cells):
        if cc != c or not SB[k]:
            continue
        pu = pu_of[i]
        if pu - 1 not in ucov:
            continue
        h1, hi = 1 + 0j, 1j
        for j in range(i + 1, pu):
            l, b = mv[j]
            h1, hi = l * h1 + b * np.conj(h1), l * hi + b * np.conj(hi)
        rows.append(k); Yu.append(ucov[pu - 1]); lam_.append((h1 - 1j * hi) / 2); mu_.append((h1 + 1j * hi) / 2)
rows, Yu, lam_, mu_ = np.array(rows), np.array(Yu), np.array(lam_), np.array(mu_)
Sb, Db, C0b, A0b = F[rows], D[rows], C0[rows], A0[rows]
print(f"sums with B, U and the carry {len(rows)}; mode {MODE}: |mu|/|lambda| median {np.median(np.abs(mu_) / np.abs(lam_)):.3f}; read in {time.time() - t0:.1f} s", flush=True)

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

cr = chi(1, C0b); cu_ex = lam_ * cr + mu_ * np.conj(cr)
print(f"the exact crossing placed at B, carried to U: share {share2(cu_ex)[0]:.4f}", flush=True)
Sc = Sb - Sb.mean(0)
Csb = Sc.T @ Sc
ev, E = np.linalg.eigh(Csb); keep = ev > 1e-9 * ev.max()
Wh = E[:, keep] / np.sqrt(ev[keep])
Xw = Sc @ Wh
yc = y - y.mean(0)
cc = np.linalg.svd(np.linalg.qr(Xw)[0].T @ np.linalg.qr(yc)[0], compute_uv=False)
print(f"the state at B alone, straight-line reads: top canonical correlations squared {cc[0]**2:.4f}, {cc[1]**2:.4f} (two channels {cc[0]**2 + cc[1]**2:.4f})", flush=True)
E2 = E[:, ::-1]
pp = (E2[:, 0] + 1j * E2[:, 1]).astype(complex)
starts = {"blind: principal 1+2, the ring's first character": (pp, chi(1, np.arange(10))),
          "blind: principal 1+2, the unit": (pp, np.ones(10, dtype=complex)),
          "outside: chi_1(a0)'s read, chi_1": (a_ideal.astype(complex), chi(1, np.arange(10)))}
describe("the outside form, unsearched", a_ideal.astype(complex), chi(1, np.arange(10)))
for nm, (a, b) in starts.items():
    t1 = time.time()
    s, a, b, t = climb(a, b, STEPS)
    describe(f"searched from {nm}", a, b, f" ({t} steps, {time.time() - t1:.1f} s)")
print(f"done in {time.time() - t0:.1f} s")
