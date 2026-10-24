"""Does the digits' coupling keep its hand when the state is read in its own complex modes?

CLASS_MODES.py read the state as 128 real coordinates. Its coupling K is then real and symmetric, so
a character chi_k and its conjugate chi_(10-k) are one eigenspace: the sum's crossing chi(a0)chi(b0)
and the difference's chi(a0)conj(chi(b0)) are not told apart, and the class factor's sense of turn is
left to the eigensolver. In the lock region its first mode was 0.79 on k=1 and 0.10 on k=9.

Here the state is read as level 0's 64 complex modes h, and a state read is holomorphic, r = b^H h
(b in C^64), so it turns with the modes. The form is c = (b^H h) beta_d, centred within each digit in
the region. After the state's common read, the digits couple through the Hermitian
K_de = tr(Sbar^-1 Mt_d Y_r^-1 Mt_e^H) / sqrt(n_d n_e), Mt_d = sum over d of h~ y^T less the common
read. Its eigenvectors keep the orientation: chi_k and chi_(10-k) separate wherever the tension
turns one way. Printed per region: K's eigenvalues and each mode's power on every character k
(not paired); the first mode's form with its best holomorphic state reads (1, 2, 4, 8 together),
read held out at the 495 sums' B cells (uncentred, as the machine reads); and an exterior check:
how much of chi_1(a0) and of chi_9(a0) a holomorphic read of the state holds at the sums' B cells
(fitted on even lines, read on odd), with that read's form crossed with the first mode and with
chi_1, held out. Uses REGION_SHARE.py (argument 1)."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])

LN = []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    lines = np.cumsum([0] + [1 if x == 10 else 0 for x in text])
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            LN.append(lines[int(line.split()[1])])
LN = np.array(LN)

def holo_heldout(B_, beta, m, hm):
    """c0 at the held-out sums' B cells from the channels (b_q^H h) beta_d of the reads B_ (columns),
    uncentred, an indicator fit at the training sums' B cells of the region (0 outside it, held out)."""
    tr = SB & m
    ct = (H[tr].conj() @ B_).conj() * beta[D[tr]][:, None]
    ch = (Hh[SBh].conj() @ B_).conj() * beta[Dh[SBh]][:, None] * hm[SBh][:, None]
    X = np.hstack([ct.real, ct.imag]); Xh = np.hstack([ch.real, ch.imag])
    sc = np.abs(X).std(0) + 1e-30
    X1 = np.hstack([X / sc, np.ones((len(X), 1))]); X1h = np.hstack([Xh / sc, np.ones((len(Xh), 1))])
    W = np.linalg.solve(X1.T @ X1 + np.eye(X1.shape[1]) * 1e-6, X1.T @ np.eye(10)[C0[tr]])
    return int((np.argmax(X1h @ W, 1) == C0h[SBh]).sum())

def run(name, m, hm):
    t1 = time.time()
    h, y, d = H[m], Yv[m], D[m]
    Yi = np.linalg.inv(y.T @ y)
    n_d = np.array([(d == q).sum() for q in range(DIG)], dtype=float)
    mu = np.array([h[d == q].mean(0) if n_d[q] else np.zeros(h.shape[1]) for q in range(DIG)])
    ht = h - mu[d]
    M = np.array([ht[d == q].T @ y[d == q] for q in range(DIG)])                  # 64 x 64 complex
    S = np.array([ht[d == q].T @ ht[d == q].conj() for q in range(DIG)])          # Hermitian
    St = S.sum(0)
    Wbar = np.linalg.solve(St, M.sum(0))
    Mt = M - np.einsum("kpq,qr->kpr", S, Wbar)
    Sbi = np.linalg.inv(St / len(h))
    K = np.einsum("pq,kqr,rs,lps->kl", Sbi, Mt, Yi, Mt.conj()) / np.sqrt(np.outer(n_d, n_d))
    herm = np.linalg.norm(K - K.conj().T) / np.linalg.norm(K)
    K = (K + K.conj().T) / 2
    w, U = np.linalg.eigh(K)
    w, U = w[::-1], U[:, ::-1]
    ch = np.array([chi(k, np.arange(10)) / math.sqrt(10) for k in range(10)])
    print(f"{name}: cells {int(m.sum())}; K's departure from Hermitian {herm:.1e}; eigenvalues {', '.join(f'{x:.4f}' for x in w)}", flush=True)
    for i in range(10):
        al = np.abs(ch.conj() @ U[:, i])**2
        top = np.argsort(al)[::-1][:2]
        print(f"   mode {i + 1}: power on k=0..9 {' '.join(f'{x:.2f}' for x in al)} (largest k={top[0]} {al[top[0]]:.2f}, then k={top[1]} {al[top[1]]:.2f})", flush=True)
    beta = U[:, 0].astype(complex)
    # the mode's best holomorphic state reads: generalized eigenvectors of N Yi N^H against sum |beta|^2 S
    N = np.einsum("k,kpq->pq", beta, Mt)
    A = N @ Yi @ N.conj().T
    Bm = np.einsum("k,kpq->pq", np.abs(beta)**2, S)
    Bm = Bm + np.eye(len(Bm)) * 1e-12 * np.trace(Bm).real / len(Bm)
    L = np.linalg.cholesky(Bm); Li = np.linalg.inv(L)
    ev, V = np.linalg.eigh(Li @ A @ Li.conj().T)
    Bq = Li.conj().T @ V[:, ::-1]
    print(f"   the first mode's form, its top state reads together, held out units at B: "
          + "; ".join(f"{r}: {holo_heldout(Bq[:, :r], beta, m, hm)} (top eigenvalues {ev[::-1][:r].sum():.4f})" for r in (1, 2, 4, 8)), flush=True)
    # exterior: a holomorphic read of chi_1(a0), chi_9(a0) at the sums' B cells of the region
    sb = SB & m
    if sb.sum() > 100:
        tr, te = sb & (LN % 2 == 0), sb & (LN % 2 == 1)
        for k in (1, 9):
            t = chi(k, A0)
            X = np.hstack([H, np.ones((len(H), 1))])
            bfit = np.linalg.solve(X[tr].conj().T @ X[tr] + np.eye(X.shape[1]) * 1e-6 * np.trace(X[tr].conj().T @ X[tr]).real / X.shape[1], X[tr].conj().T @ t[tr])
            r = t[te] - X[te] @ bfit
            r2 = 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()
            b = bfit[:-1].conj()[:, None]                    # read = b^H h
            print(f"   a holomorphic read of chi_{k}(a0) at the sums' B cells holds {r2:.3f}; its form held out with the first mode {holo_heldout(b, beta, m, hm)}, "
                  f"with chi_1 {holo_heldout(b, chi(1, np.arange(10)), m, hm)}, with chi_9 {holo_heldout(b, chi(9, np.arange(10)), m, hm)} of {int(SBh.sum())}", flush=True)
    print(f"   {time.time() - t1:.1f} s", flush=True)

sec = np.floor((np.angle(H[:, 42] * np.conj(H[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
sech = np.floor((np.angle(Hh[:, 42] * np.conj(Hh[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
run("every digit arrival", np.ones(len(F), bool), np.ones(len(Fh), bool))
run("lock 42-35 sector 0", sec == 0, sech == 0)
run("the sums' B cells (label region)", SB, SBh)
run("the differences' B cells (label region)", ROLE & (OP == "-"), np.zeros(len(Fh), bool))
print(f"done in {time.time() - t0:.1f} s")
