"""A founding inside one region, at the region's own loudness: how many forms before the sum's units
are read? Uses the loading, the region and the search of REGION_SHARE.py (argument 1; its reports
are not run). In a region r, forms c = (a^T s)(beta_d) are founded one rank at a time, each maximizing
the circular criterion of what it adds to the forms already founded (its channels' part orthogonal
to theirs, inside r), in r's own tension Y_r. After each rank:
- the forms' joint canonical share in r (the sum of their squared canonical correlations);
- the exact crossing chi_1(c0) at the region's training sums' B cells (a label): its share in r
  left after the founded forms (the part of it they have not yet bridged);
- beta's nearest character of the ring of ten (k = 0 is a read of the state alone);
- held out: the sums' units at B read from all the founded channels together, as the machine reads
  them (uncentred), by a straight-line indicator fit at the training sums' B cells of r; a held-out
  cell outside r receives nothing.
Regions: the lock 42-35 sector 0; with the argument "all", also the sums' B cells alone (a label
region: the ceiling) and every digit arrival. With the argument "state", the founding starts after
the state's own read (all 128 coordinates of the state, one read for every arriving digit), so each
form founds only what the arriving digit changes; the held-out read uses the founded forms alone."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])
RANKS = int(sys.argv[2])

def found(name, m, hm):
    t1 = time.time()
    reg = Region(m)
    n, fc, y, d = reg.n, reg.fc, reg.y, reg.d
    tr = SB[m]
    ex = np.where(tr, chi(1, np.where(tr, C0[m], 0)), 0)
    X = np.stack([ex.real, ex.imag], 1)
    for k in range(DIG):
        q = d == k; X[q] -= X[q].mean(0)
    P = np.zeros((n, 0)); Pr = np.zeros((n, 0)); Ph = np.zeros((len(Fh), 0))
    def joint(C):
        R, G = C.T @ y, C.T @ C
        return np.trace(reg.Yi @ R.T @ np.linalg.solve(G + np.eye(len(G)) * 1e-12 * np.trace(G), R))
    print(f"{name}: cells {n}, sums' B cells {int(tr.sum())}; the exact crossing's share {joint(X):.4f}", flush=True)
    if "state" in sys.argv[3:]:
        # the state's own read first: every coordinate of the state, the same for every arriving digit
        P = fc.copy()
        print(f"   the state's own read (128 channels, common to the digits): share {joint(P):.4f}; the crossing left {joint(X - P @ np.linalg.solve(P.T @ P, P.T @ X)):.4f}", flush=True)
    for r in range(RANKS):
        q = P.shape[1]
        if q:
            GPi = np.linalg.inv(P.T @ P); YP = y.T @ P
            Q = np.array([P[d == k].T @ fc[d == k] for k in range(DIG)])
        else:
            GPi = np.zeros((0, 0)); YP = np.zeros((64, 0)); Q = np.zeros((DIG, 0, F.shape[1]))
        def J(a, b):
            Ns = np.einsum("k,kpq->qp", b, reg.M); Qs = np.einsum("k,kqp->qp", b, Q)
            Nn = Ns @ a - YP @ GPi @ (Qs @ a)
            den = sum(abs(b[k])**2 * (a.conj() @ reg.S[k] @ a).real for k in range(DIG)) - ((Qs @ a).conj() @ GPi @ (Qs @ a)).real
            return (Nn.conj() @ reg.Yi @ Nn).real / den
        def search(a, b, steps=300):
            j = J(a, b)
            for _ in range(steps):
                U = np.einsum("kpq,p->qk", reg.M, a); W = np.einsum("kqp,p->qk", Q, a)
                p = np.array([(a.conj() @ reg.S[k] @ a).real for k in range(DIG)])
                Ut = U - YP @ GPi @ W
                _, b = geneig_top(Ut.conj().T @ reg.Yi @ Ut, np.diag(p) - W.conj().T @ GPi @ W)
                Ns = np.einsum("k,kpq->qp", b, reg.M); Qs = np.einsum("k,kqp->qp", b, Q)
                N = Ns - YP @ GPi @ Qs
                _, a = geneig_top(N.conj().T @ reg.Yi @ N, np.einsum("k,kpq->pq", np.abs(b)**2, reg.S) - Qs.conj().T @ GPi @ Qs)
                jn = J(a, b)
                if jn - j <= 1e-10 * abs(j):
                    return jn, a, b
                j = jn
            return j, a, b
        st = reg.starts()
        best = max((search(*st[s]) + (s,) for s in ("ring", "outside")), key=lambda t: t[0])
        j, a, b, s = best
        c = (fc @ a) * b[d]
        P = np.hstack([P, np.stack([c.real, c.imag], 1)])
        cr = (F[m] @ a) * b[d]
        Pr = np.hstack([Pr, np.stack([cr.real, cr.imag], 1)])
        ch = (Fh @ a) * b[Dh] * hm
        Ph = np.hstack([Ph, np.stack([ch.real, ch.imag], 1)])
        # the crossing's part left: its share after the founded channels
        Xr = X - P @ np.linalg.solve(P.T @ P, P.T @ X)
        left = joint(Xr)
        # held out
        sc = np.abs(Pr[tr]).std(0) + 1e-30
        A = np.hstack([Pr[tr] / sc, np.ones((int(tr.sum()), 1))])
        Wt = np.linalg.solve(A.T @ A + np.eye(A.shape[1]) * 1e-6, A.T @ np.eye(10)[C0[m][tr]])
        Ah = np.hstack([Ph[SBh] / sc, np.ones((int(SBh.sum()), 1))])
        held = int((np.argmax(Ah @ Wt, 1) == C0h[SBh]).sum())
        trained = int((np.argmax(A @ Wt, 1) == C0[m][tr]).sum())
        chs = character_of(b); k = int(np.argmax(chs[1:])) + 1
        print(f"   rank {r + 1} ({s}): adds J {j:.4f}; joint share {joint(P):.4f}; the crossing left {left:.4f}; beta k=0 {chs[0]:.2f}, nearest k={k} {chs[k]:.2f}; sums' units at B: training {trained} of {int(tr.sum())}, held out {held} of {int(SBh.sum())}; {time.time() - t1:.1f} s", flush=True)

for j, k in ((42, 35),):
    sec = np.floor((np.angle(H[:, j] * np.conj(H[:, k])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
    sech = np.floor((np.angle(Hh[:, j] * np.conj(Hh[:, k])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
    found(f"lock {j}-{k} sector 0", sec == 0, sech == 0)
if "all" in sys.argv[3:]:
    found("the sums' B cells (label region)", SB, SBh)
    found("every digit arrival", np.ones(len(F), bool), np.ones(len(Fh), bool))
print(f"done in {time.time() - t0:.1f} s")
