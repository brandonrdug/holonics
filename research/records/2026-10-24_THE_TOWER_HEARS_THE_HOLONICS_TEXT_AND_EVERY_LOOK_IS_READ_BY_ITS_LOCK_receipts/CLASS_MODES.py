"""The arriving digits' own modes of the tension. After the state's own read (one read of the state
for every arriving digit, removed from the tension), what is left at a digit arrival depends on
which digit arrives. The digits couple through it: K_de = tr(Y_r^-1 Mt_d^T Sbar^-1 Mt_e) / sqrt(n_d n_e),
with Mt_d the state-tension moment of digit d left after the common read and Sbar the state's
common within-digit Gram per cell. K is read in the region's own unit. Its eigenvectors are the
digits' modes of the tension, located from the tension itself. If the tension is carried by the
ring of ten (shifting the arriving digit as the first operand's units shift back), K is circulant
and its modes are the characters chi_k, in pairs (k, 10 - k).

For each of K's modes (a pair of eigenvectors with near-equal eigenvalues taken as one complex
factor e1 + i e2): its alignment with the characters, and the form whose class factor is that mode
and whose state read is the best for it (a by the generalized eigenproblem, after the common read):
its added share, and the sums' units it reads held out (uncentred, through the form alone).
Uses the loading and the region of REGION_SHARE.py (argument 1). Regions: every digit arrival and
the lock 42-35 sector 0; with the argument "labels", instead the label regions (the sums' B cells,
and the B cells of all three operations), as ceilings."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])

def modes(name, m, hm):
    t1 = time.time()
    reg = Region(m)
    n_d = np.array([(reg.d == k).sum() for k in range(DIG)], dtype=float)
    S = reg.S.sum(0)
    Wbar = np.linalg.solve(S, reg.M.sum(0))
    Mt = reg.M - np.einsum("kpq,qr->kpr", reg.S, Wbar)
    Sbar = S / reg.n
    Z = np.array([np.linalg.solve(Sbar, Mt[k]) for k in range(DIG)])
    K = np.einsum("kpq,qr,lpr->kl", Mt, reg.Yi, Z) / np.sqrt(np.outer(n_d, n_d))
    K = (K + K.T) / 2
    w, U = np.linalg.eigh(K)
    w, U = w[::-1], U[:, ::-1]
    print(f"{name}: cells {reg.n}; K's eigenvalues: {', '.join(f'{x:.4f}' for x in w)}", flush=True)
    ch = np.array([chi(k, np.arange(10)) / math.sqrt(10) for k in range(10)])
    for i in range(10):
        al = np.abs(ch.conj() @ U[:, i])**2   # power of eigenvector i on each character
        pw = {k: al[k] + (al[10 - k] if 0 < k < 5 else 0) for k in range(6)}
        best = max(pw, key=pw.get)
        print(f"   mode {i + 1}: power on the characters {', '.join(f'k={k}|{10-k}' if 0 < k < 5 else f'k={k}' for k in range(6))}: "
              f"{', '.join(f'{pw[k]:.2f}' for k in range(6))}", flush=True)
    # forms from mode pairs (1,2), (3,4), (5,6) and singles
    Pc = reg.fc
    GPi = np.linalg.inv(Pc.T @ Pc); YP = reg.y.T @ Pc
    Q = np.array([Pc[reg.d == k].T @ reg.fc[reg.d == k] for k in range(DIG)])
    for (i, j) in ((0, 1), (2, 3), (4, 5), (6, 7)):
        b = (U[:, i] + 1j * U[:, j]).astype(complex)
        Ns = np.einsum("k,kpq->qp", b, reg.M); Qs = np.einsum("k,kqp->qp", b, Q)
        N = Ns - YP @ GPi @ Qs
        Bm = np.einsum("k,kpq->pq", np.abs(b)**2, reg.S) - Qs.conj().T @ GPi @ Qs
        J, a = geneig_top(N.conj().T @ reg.Yi @ N, Bm)
        al = character_of(b); k = int(np.argmax(al[1:])) + 1
        print(f"   the form on modes {i + 1}+{j + 1}: adds J {J:.4f}; beta nearest k={k} ({al[k]:.2f}; k=0 {al[0]:.2f}); held out, sums' units at B {read_heldout(a, b, reg, hm)} of {int(SBh.sum())}", flush=True)
        # the mode's several state reads: the top r generalized eigenvectors, read together
        Bm = Bm + np.eye(len(Bm)) * 1e-12 * np.trace(Bm).real / len(Bm)
        L = np.linalg.cholesky(Bm); Li = np.linalg.inv(L)
        ev, Uv = np.linalg.eigh(Li @ (N.conj().T @ reg.Yi @ N) @ Li.conj().T)
        A_ = Li.conj().T @ Uv[:, ::-1]
        outs = []
        for r in (1, 2, 4, 8):
            tr = SB & reg.m
            ct = np.hstack([np.stack([((F[tr] @ A_[:, q]) * b[D[tr]]).real, ((F[tr] @ A_[:, q]) * b[D[tr]]).imag], 1) for q in range(r)])
            chh = np.hstack([np.stack([((Fh[SBh] @ A_[:, q]) * b[Dh[SBh]] * hm[SBh]).real, ((Fh[SBh] @ A_[:, q]) * b[Dh[SBh]] * hm[SBh]).imag], 1) for q in range(r)])
            sc = np.abs(ct).std(0) + 1e-30
            X1 = np.hstack([ct / sc, np.ones((len(ct), 1))]); Xh = np.hstack([chh / sc, np.ones((len(chh), 1))])
            Wt = np.linalg.solve(X1.T @ X1 + np.eye(X1.shape[1]) * 1e-6, X1.T @ np.eye(10)[C0[tr]])
            # the same read with the arriving digit's indicator beside the channels: a per-digit offset
            # of the form (its class mean, which the founding's criterion does not see) is then read away
            O, Oh = np.eye(10)[D[tr]], np.eye(10)[Dh[SBh]]
            X2 = np.hstack([ct / sc, O]); X2h = np.hstack([chh / sc, Oh])
            W2 = np.linalg.solve(X2.T @ X2 + np.eye(X2.shape[1]) * 1e-6, X2.T @ np.eye(10)[C0[tr]])
            outs.append(f"{r}: {int((np.argmax(Xh @ Wt, 1) == C0h[SBh]).sum())}, offsets read away {int((np.argmax(X2h @ W2, 1) == C0h[SBh]).sum())} (top eigenvalues {ev[::-1][:r].sum():.4f})")
        print(f"      its top state reads together, held out units at B: " + "; ".join(outs), flush=True)
    if name == "every digit arrival":
        tr = SB & reg.m
        O, Oh = np.eye(10)[D[tr]], np.eye(10)[Dh[SBh]]
        W0 = np.linalg.solve(O.T @ O + np.eye(10) * 1e-6, O.T @ np.eye(10)[C0[tr]])
        print(f"   the arriving digit alone (no form), held out units at B: {int((np.argmax(Oh @ W0, 1) == C0h[SBh]).sum())}", flush=True)
        for nm, (a_, b_) in (("the outside form", (a_ideal, beta_ideal)),):
            ct = (F[tr] @ a_) * b_[D[tr]]; chh = (Fh[SBh] @ a_) * b_[Dh[SBh]]
            ct, chh = np.stack([ct.real, ct.imag], 1), np.stack([chh.real, chh.imag], 1)
            sc = np.abs(ct).std(0)
            X2 = np.hstack([ct / sc, O]); X2h = np.hstack([chh / sc, Oh])
            W2 = np.linalg.solve(X2.T @ X2 + np.eye(X2.shape[1]) * 1e-6, X2.T @ np.eye(10)[C0[tr]])
            print(f"   {nm}, offsets read away: {int((np.argmax(X2h @ W2, 1) == C0h[SBh]).sum())}", flush=True)
    print(f"   {time.time() - t1:.1f} s", flush=True)

if "labels" in sys.argv[2:]:
    # label regions, as ceilings: the sums' B cells alone, and the B cells of all three operations
    modes("the sums' B cells (label region)", SB, SBh)
    modes("the B cells of all three operations (label region)", ROLE, np.ones(len(Fh), bool))
    print(f"done in {time.time() - t0:.1f} s"); sys.exit(0)
modes("every digit arrival", np.ones(len(F), bool), np.ones(len(Fh), bool))
sec = np.floor((np.angle(H[:, 42] * np.conj(H[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
sech = np.floor((np.angle(Hh[:, 42] * np.conj(Hh[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
modes("lock 42-35 sector 0", sec == 0, sech == 0)
print(f"done in {time.time() - t0:.1f} s")
