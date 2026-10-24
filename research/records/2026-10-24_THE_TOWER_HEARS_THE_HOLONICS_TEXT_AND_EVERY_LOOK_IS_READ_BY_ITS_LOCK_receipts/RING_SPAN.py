"""Forms whose class factor is held in the ring's pair of coupling modes.

HANDED_RING.py found the Hermitian coupling's top two modes spanning the first character and its
conjugate (k=1 and k=9) about equally: the state carries each arrival in both senses (the pump's
conjugate term), so the sense of turn is fixed only by pairing a read with a class factor. Here the
class factor beta is held in the span of K's top two modes (no constant, so a read of the state
alone is excluded) and the holomorphic state read b is searched jointly with it, alternating:
for fixed b, beta is the top eigenvector of the two-by-two problem in the span; for fixed beta, b is
the top generalized eigenvector. Ranks are founded one after another, each read kept S-orthogonal to
the reads before it. Each start: beta = u1, u2, (u1 + i u2)/sqrt2, (u1 - i u2)/sqrt2; the rank keeps
the largest J. Printed per rank: J, beta's power on k=1 and k=9, the read's held fraction (exterior,
fitted on even lines, read on odd) of chi_1(a0), chi_1(a1), chi_1(b1) at the region's sums' B cells,
and the units at B held out from the ranks so far together (uncentred). Uses REGION_SHARE.py and
HANDED_RING.py's loading (arguments 1 and 2)."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])
src2 = open(sys.argv[2]).read()
exec(src2[src2.index("LN = []"):src2.index("def run")])

cols = []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    pos = {}
    start = 0
    for line in text.split(b"\n"):
        m_ = tm.tower_circuit.EQ.match(line)
        if m_:
            a_, op_, b_, c_ = m_.groups()
            t = lambda s, i: int(s[-1 - i:len(s) - i]) if len(s) > i else -1
            pos[start + len(a_) + len(b_)] = (t(a_, 1), t(b_, 1))
        start += len(line) + 1
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            cols.append(pos.get(int(line.split()[1]), (-1, -1)))
A1x, B1x = np.array(cols).T

def held(x, t, ok):
    tr, te = ok & (LN % 2 == 0), ok & (LN % 2 == 1)
    A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
    s = np.abs(A[tr]).std(0) + 1e-30
    W = np.linalg.solve((A[tr] / s).T @ (A[tr] / s) + np.eye(3) * 1e-9, (A[tr] / s).T @ t[tr])
    r = t[te] - (A[te] / s) @ W
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()

def run(name, m, hm, ranks=4):
    t1 = time.time()
    h, y, d = H[m], Yv[m], D[m]
    Yi = np.linalg.inv(y.T @ y)
    n_d = np.array([(d == q).sum() for q in range(DIG)], dtype=float)
    mu = np.array([h[d == q].mean(0) if n_d[q] else np.zeros(h.shape[1]) for q in range(DIG)])
    ht = h - mu[d]
    M = np.array([ht[d == q].T @ y[d == q] for q in range(DIG)])
    S = np.array([ht[d == q].T @ ht[d == q].conj() for q in range(DIG)])
    St = S.sum(0)
    Mt = M - np.einsum("kpq,qr->kpr", S, np.linalg.solve(St, M.sum(0)))
    K = np.einsum("pq,kqr,rs,lps->kl", np.linalg.inv(St / len(h)), Mt, Yi, Mt.conj()) / np.sqrt(np.outer(n_d, n_d))
    w, U = np.linalg.eigh((K + K.conj().T) / 2)
    Us = U[:, ::-1][:, :2]                       # the ring's pair: beta = Us g, g in C^2
    def J(b, beta):
        mm = np.einsum("k,p,kpq->q", beta, b.conj(), M)
        den = sum(abs(beta[k])**2 * (b.conj() @ S[k] @ b).real for k in range(DIG))
        return (mm @ Yi @ mm.conj()).real / den
    def step_b(beta, Pb):
        N = np.einsum("k,kpq->pq", beta, M)
        A = N @ Yi @ N.conj().T
        B = np.einsum("k,kpq->pq", np.abs(beta)**2, S)
        if Pb is not None:                       # restrict b to the S-orthogonal complement of the earlier reads
            Q = Pb
            A, B = Q.conj().T @ A @ Q, Q.conj().T @ B @ Q
        B = B + np.eye(len(B)) * 1e-12 * np.trace(B).real / len(B)
        L = np.linalg.cholesky(B); Li = np.linalg.inv(L)
        ev, V = np.linalg.eigh(Li @ A @ Li.conj().T)
        x = Li.conj().T @ V[:, -1]
        return (Pb @ x) if Pb is not None else x
    def step_g(b):
        V = np.einsum("p,kpq->qk", b.conj(), M) @ Us          # 64 x 2
        p = np.array([(b.conj() @ S[k] @ b).real for k in range(DIG)])
        B = Us.conj().T @ np.diag(p) @ Us
        _, g = geneig_top(V.conj().T @ Yi @ V, B)
        return Us @ g
    found, Ball = [], []
    sb = SB & m
    starts = {"u1": Us[:, 0], "u2": Us[:, 1], "u1+iu2": (Us[:, 0] + 1j * Us[:, 1]) / math.sqrt(2), "u1-iu2": (Us[:, 0] - 1j * Us[:, 1]) / math.sqrt(2)}
    print(f"{name}: cells {int(m.sum())}; the ring's pair on k=1 / k=9: u1 {abs(chi(1, np.arange(10)).conj() @ Us[:, 0])**2 / 10:.2f}/{abs(chi(9, np.arange(10)).conj() @ Us[:, 0])**2 / 10:.2f}, "
          f"u2 {abs(chi(1, np.arange(10)).conj() @ Us[:, 1])**2 / 10:.2f}/{abs(chi(9, np.arange(10)).conj() @ Us[:, 1])**2 / 10:.2f}", flush=True)
    for r in range(ranks):
        if Ball:
            Bp = np.array(Ball).T                                 # S-orthogonal complement of earlier reads
            G = Bp.conj().T @ St
            _, s_, Vh = np.linalg.svd(G)
            Pb = Vh[len(Ball):].conj().T
        else:
            Pb = None
        best = None
        for sn, beta in starts.items():
            j = None
            for _ in range(200):
                b = step_b(beta, Pb)
                beta = step_g(b)
                jn = J(b, beta)
                if j is not None and jn - j <= 1e-9 * abs(j):
                    j = jn; break
                j = jn
            if best is None or j > best[0]:
                best = (j, b, beta, sn)
        j, b, beta, sn = best
        Ball.append(b); found.append((b, beta))
        p1 = abs(chi(1, np.arange(10)).conj() @ beta)**2 / (10 * np.linalg.norm(beta)**2)
        p9 = abs(chi(9, np.arange(10)).conj() @ beta)**2 / (10 * np.linalg.norm(beta)**2)
        x = (H.conj() @ b).conj()
        tg = {"a0": (chi(1, A0), sb & (A0 >= 0)), "a1": (chi(1, A1x), sb & (A1x >= 0)), "b1": (chi(1, B1x), sb & (B1x >= 0))}
        hs = ", ".join(f"chi_1({nm}) {held(x, t, ok):.3f}" for nm, (t, ok) in tg.items())
        # held out: all ranks so far together
        tr = sb
        ct = np.hstack([np.stack([((H[tr].conj() @ bb).conj() * bt[D[tr]]).real, ((H[tr].conj() @ bb).conj() * bt[D[tr]]).imag], 1) for bb, bt in found])
        chh = np.hstack([np.stack([((Hh[SBh].conj() @ bb).conj() * bt[Dh[SBh]] * hm[SBh]).real, ((Hh[SBh].conj() @ bb).conj() * bt[Dh[SBh]] * hm[SBh]).imag], 1) for bb, bt in found])
        sc = np.abs(ct).std(0) + 1e-30
        X1 = np.hstack([ct / sc, np.ones((len(ct), 1))]); X1h = np.hstack([chh / sc, np.ones((len(chh), 1))])
        W = np.linalg.solve(X1.T @ X1 + np.eye(X1.shape[1]) * 1e-6, X1.T @ np.eye(10)[C0[tr]])
        ho = int((np.argmax(X1h @ W, 1) == C0h[SBh]).sum())
        print(f"   rank {r + 1} (from {sn}): J {j:.4f}; beta on k=1 {p1:.2f}, k=9 {p9:.2f}; the read holds {hs}; held out, ranks 1..{r + 1} together, units at B {ho} of {int(SBh.sum())}; {time.time() - t1:.1f} s", flush=True)

sec = np.floor((np.angle(H[:, 42] * np.conj(H[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
sech = np.floor((np.angle(Hh[:, 42] * np.conj(Hh[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
run("lock 42-35 sector 0", sec == 0, sech == 0)
run("the sums' B cells (label region)", SB, SBh)
print(f"done in {time.time() - t0:.1f} s")
