"""What state read does the tension pair with the arriving digit's first character mode? In the
label region of the sums' B cells, after the state's own read, the digits' coupling K (as in
CLASS_MODES.py) is diagonalized; its modes 1 and 2 form the class factor beta = e1 + i e2 (aligned
0.93 with the first character). The state reads paired with it are the top generalized
eigenvectors (as in CLASS_MODES.py). Each read a^T s (complex) is fitted, at the training sums' B
cells, to the first character of: the first operand's units a0, its tens a1, the second operand's
tens b1, the result's tens c1 (0 where absent), and to the carry [a0 + b0 >= 10]; fitted on even
lines and read on odd (the fraction of the target's variance held). Uses REGION_SHARE.py (argument 1)."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])

digits = {}
k = 0
cols = []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    pos = {}
    start = 0
    for line in text.split(b"\n"):
        m_ = tm.tower_circuit.EQ.match(line)
        if m_:
            a_, op_, b_, c_ = m_.groups()
            t = lambda s, i: int(s[-1 - i:len(s) - i]) if len(s) > i else 0
            pos[start + len(a_) + len(b_)] = (t(a_, 0), t(a_, 1), t(b_, 0), t(b_, 1), t(c_, 1))
        start += len(line) + 1
    lines = np.cumsum([0] + [1 if x == 10 else 0 for x in text])
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            i = int(line.split()[1])
            cols.append(pos.get(i, (-1,) * 5) + (lines[i],))
cols = np.array(cols)
A0_, A1_, B0_, B1_, C1_, LN = cols.T
m = SB
reg = Region(m)
n_d = np.array([(reg.d == q).sum() for q in range(DIG)], dtype=float)
S = reg.S.sum(0)
Wbar = np.linalg.solve(S, reg.M.sum(0))
Mt = reg.M - np.einsum("kpq,qr->kpr", reg.S, Wbar)
Sbar = S / reg.n
Z = np.array([np.linalg.solve(Sbar, Mt[q]) for q in range(DIG)])
K = np.einsum("kpq,qr,lpr->kl", Mt, reg.Yi, Z) / np.sqrt(np.outer(n_d, n_d))
w, U = np.linalg.eigh((K + K.T) / 2)
U = U[:, ::-1]
b = (U[:, 0] + 1j * U[:, 1]).astype(complex)
Pc = reg.fc
GPi = np.linalg.inv(Pc.T @ Pc); YP = reg.y.T @ Pc
Q = np.array([Pc[reg.d == q].T @ reg.fc[reg.d == q] for q in range(DIG)])
Ns = np.einsum("k,kpq->qp", b, reg.M); Qs = np.einsum("k,kqp->qp", b, Q)
N = Ns - YP @ GPi @ Qs
Bm = np.einsum("k,kpq->pq", np.abs(b)**2, reg.S) - Qs.conj().T @ GPi @ Qs
Bm = Bm + np.eye(len(Bm)) * 1e-12 * np.trace(Bm).real / len(Bm)
L = np.linalg.cholesky(Bm); Li = np.linalg.inv(L)
ev, Uv = np.linalg.eigh(Li @ (N.conj().T @ reg.Yi @ N) @ Li.conj().T)
Aq = Li.conj().T @ Uv[:, ::-1]
ln = LN[m]; tr, te = ln % 2 == 0, ln % 2 == 1
f = F[m]
targets = {"chi1(a0)": np.exp(2j*np.pi*A0_[m]/10), "chi1(a1)": np.exp(2j*np.pi*A1_[m]/10), "chi1(b1)": np.exp(2j*np.pi*B1_[m]/10),
           "chi1(c1)": np.exp(2j*np.pi*C1_[m]/10), "carry": ((A0_[m] + B0_[m]) >= 10).astype(complex)}
def held(x, t):
    A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
    s = np.abs(A[tr]).std(0) + 1e-30
    W = np.linalg.solve((A[tr]/s).T @ (A[tr]/s) + np.eye(3) * 1e-9, (A[tr]/s).T @ t[tr])
    r = t[te] - (A[te]/s) @ W
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()
print(f"label region (sums' B cells) {reg.n}; class factor's first-character alignment {character_of(b)[1]:.2f} / {character_of(b)[9]:.2f} (k=1 / k=9)")
for q in range(4):
    x = f @ Aq[:, q]
    print(f"   state read {q + 1} (eigenvalue {ev[::-1][q]:.4f}): " + ", ".join(f"{nm} {held(x, t):.3f}" for nm, t in targets.items()))
x = f @ a_ideal
print(f"   the outside form's read: " + ", ".join(f"{nm} {held(x, t):.3f}" for nm, t in targets.items()))
print(f"done in {time.time() - t0:.1f} s")
