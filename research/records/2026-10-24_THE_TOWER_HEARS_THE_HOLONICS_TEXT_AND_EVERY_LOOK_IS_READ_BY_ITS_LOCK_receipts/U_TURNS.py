"""The blind reading at U: the carried turns, their crossings, ranked by two-channel share.

U_FORMS.py found that at U, the cell coding a sum's units, the exact crossing chi_1(c0) holds 1.86 of
the 2 its two channels can hold at the region's own loudness, while searches from the state's
principal directions stop on forms that read nothing. Here no label chooses the reads:
1. the carried turns: over the region's cells (the 8,986 training sums' U cells, a label region),
   reads of the state whitened in the region whose modulus is constant (Godard's criterion,
   minimize E(|z|^2 - 1)^2), found one after another, each decorrelated from those before it, each
   from the whitened principal pair in order;
2. their crossings in both senses, z_i z_j (with the squares) and z_i conj(z_j), the reads centred
   at the region's training mean (a constant at the receiver; the same mean held out);
3. every crossing ranked by its two-channel share tr(G^-1 R Y_r^-1 R^T) at the region's own
   loudness, the measure that counts a turn's two channels (max 2).
Printed: each turn's modulus spread and, for a0, b0 and c0, the character chi_k (k = 1..5; chi_(10-k) is
its conjugate, the same two real channels) it holds most and how much (fitted on even lines, read on
odd); the top crossings with their share, J, the character of c0 and of the difference a0 - b0 they
hold most and how much, the share of each exact character chi_k(c0) at the region (a label ceiling), and the units at U read held out from each
alone and from the top 1, 2, 4, 8 together (uncentred indicator fit at the training U cells).
The labels only read what the blind ranking found. Uses U_FORMS.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
exec(src[:src.index("# references")])
NCOMP, ITERS = int(sys.argv[2]), int(sys.argv[3])

def godard(X, w, iters):
    def cost(w):
        z = X @ w
        return ((np.abs(z)**2 - 1)**2).mean(), z
    j, z = cost(w)
    step = 0.5
    for _ in range(iters):
        g = 4 * (X.T @ ((np.abs(z)**2 - 1) * z)) / len(X)
        while True:
            wn = w - step * g
            jn, zn = cost(wn)
            if jn < j or step < 1e-8:
                break
            step /= 2
        if j - jn <= 1e-10 * j:
            w, j, z = wn, jn, zn
            break
        w, j, z = wn, jn, zn
        step *= 1.5
    return w, j

def best_char(x, d, nm):
    v = [(held_frac(x, chi(k, d)), k) for k in range(1, 6)]
    f, k = max(v)
    return f"chi_{k}({nm}) {f:.3f}"

Sc = S_ - mu_s
Shc = Sh - mu_s
C = Sc.T @ Sc / len(Sc)
ev, E = np.linalg.eigh(C)
keep = ev > 1e-9 * ev.max()
ev, E = ev[keep][::-1], E[:, keep][:, ::-1]
Wh = E / np.sqrt(ev)
X = Sc @ Wh
print(f"whitened rank {X.shape[1]}; {NCOMP} turns, at most {ITERS} steps each", flush=True)
turns, found = [], []
t1 = time.time()
for q in range(NCOMP):
    w0 = np.zeros(X.shape[1], dtype=complex); w0[2 * q] = 1; w0[2 * q + 1] = 1j
    P = np.array(found).T if found else None
    Xq = X if P is None else X - (X @ P) @ np.linalg.pinv(P)
    w, j = godard(Xq, w0, ITERS)
    if P is not None:
        w = w - P @ (np.linalg.pinv(P) @ w)
    found += [w.real, w.imag]
    a = Wh @ w
    z = Sc @ a
    s = math.sqrt((np.abs(z)**2).mean()); a = a / s; z = z / s
    turns.append(a)
    mod = np.abs(z)
    print(f"   turn {q + 1}: modulus spread {mod.std() / mod.mean():.3f}, Godard cost {j:.4f}; holds {best_char(z, A0, 'a0')}, "
          f"{best_char(z, B0, 'b0')}, {best_char(z, C0, 'c0')}; {time.time() - t1:.1f} s", flush=True)

Z = np.array([Sc @ a for a in turns]).T
Zh = np.array([Shc @ a for a in turns]).T
prods = []
for i in range(NCOMP):
    for k in range(i, NCOMP):
        prods.append((f"z{i + 1} z{k + 1}", Z[:, i] * Z[:, k], Zh[:, i] * Zh[:, k]))
        if k > i:
            prods.append((f"z{i + 1} conj(z{k + 1})", Z[:, i] * Z[:, k].conj(), Zh[:, i] * Zh[:, k].conj()))
t2 = time.time()
ranked = sorted(((share(cv), nm, cv, cvh) for nm, cv, cvh in prods), key=lambda r: -r[0])
print(f"{len(prods)} crossings ranked by share in {time.time() - t2:.1f} s; the exact characters of c0 would hold (a label ceiling) "
      + ", ".join(f"chi_{k} {share(chi(k, C0)):.4f}" for k in range(1, 6)), flush=True)
for r, (sh, nm, cv, cvh) in enumerate(ranked[:12]):
    print(f"   {r + 1}. {nm}: share {sh:.4f}, J {J(cv):.4f}; holds {best_char(cv, C0, 'c0')}, {best_char(cv, A0 - B0, 'a0-b0')}; "
          f"held out, units at U {heldout(cv, cvh)} of {len(Sh)}", flush=True)

def heldout_many(cvs, cvhs):
    Xt = np.hstack([np.stack([c.real, c.imag], 1) for c in cvs]); sc = np.abs(Xt).std(0) + 1e-30
    Xh = np.hstack([np.stack([c.real, c.imag], 1) for c in cvhs])
    X1 = np.hstack([Xt / sc, np.ones((len(Xt), 1))]); X1h = np.hstack([Xh / sc, np.ones((len(Xh), 1))])
    W = np.linalg.solve(X1.T @ X1 + np.eye(X1.shape[1]) * 1e-6, X1.T @ np.eye(10)[C0])
    return int((np.argmax(X1h @ W, 1) == C0h).sum())

print("   held out, the top crossings together: " + "; ".join(
    f"top {r}: {heldout_many([x[2] for x in ranked[:r]], [x[3] for x in ranked[:r]])}" for r in (1, 2, 4, 8)) + f" of {len(Sh)}", flush=True)
print(f"done in {time.time() - t0:.1f} s")
