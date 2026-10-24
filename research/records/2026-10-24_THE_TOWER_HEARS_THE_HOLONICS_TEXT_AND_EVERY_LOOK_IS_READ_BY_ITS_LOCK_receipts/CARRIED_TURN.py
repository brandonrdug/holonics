"""Does the state carry its earlier arrivals as turns, and can a read of constant modulus find them
without a label? A digit's character chi_1(d) = e^(2 pi i d/10) has modulus one: a pure turn. A read
of the state that carries one earlier arrival's character is then a read whose value turns without
boosting: its modulus is the same at every cell. The constant-modulus criterion (Godard's blind
equalizer) asks only that: over a region's cells, minimize E(|a^T s|^2 - 1)^2 over complex reads a,
with the state whitened in the region. It uses no label and no arrival index; the carried arrival
and character are whatever the minimum turns with.

Components are found one after another, each read decorrelated from the reads before it (deflation),
each from a fixed start (the region's whitened principal pairs, in order). For each: its modulus
spread (std |z| / mean |z|) and, at the region's training sums' B cells, the fraction of the
variance it holds of the first character of the first operand's units a0, its tens a1 and the
second operand's tens b1 (each only where present), fitted on even lines and read on odd. Then the
form whose state factor is that read and whose class factor is the digits' first coupling mode (modes
1 and 2 of K, as in CLASS_MODES.py) is read held out at the 495 sums' B cells (uncentred, through the
region), beside the same read crossed with the exact first character chi_1. The outside read
(char/ideal_quiet.txt) is given the same measures. Uses REGION_SHARE.py (argument 1)."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])

# the operands' digits at each training digit arrival (the sums' B cells), read from the passage
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
            pos[start + len(a_) + len(b_)] = (t(a_, 0), t(a_, 1), t(b_, 1))
        start += len(line) + 1
    lines = np.cumsum([0] + [1 if x == 10 else 0 for x in text])
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            i = int(line.split()[1])
            cols.append(pos.get(i, (-1,) * 3) + (lines[i],))
cols = np.array(cols)
A0x, A1x, B1x, LN = cols.T

def coupling_mode(reg):
    n_d = np.array([(reg.d == q).sum() for q in range(DIG)], dtype=float)
    S = reg.S.sum(0)
    Wbar = np.linalg.solve(S, reg.M.sum(0))
    Mt = reg.M - np.einsum("kpq,qr->kpr", reg.S, Wbar)
    Z = np.array([np.linalg.solve(S / reg.n, Mt[q]) for q in range(DIG)])
    K = np.einsum("kpq,qr,lpr->kl", Mt, reg.Yi, Z) / np.sqrt(np.outer(n_d, n_d))
    w, U = np.linalg.eigh((K + K.T) / 2)
    U = U[:, ::-1]
    return (U[:, 0] + 1j * U[:, 1]).astype(complex)

def held(x, t, ok, ln):
    tr, te = ok & (ln % 2 == 0), ok & (ln % 2 == 1)
    A = np.stack([x.real, x.imag, np.ones(len(x))], 1)
    s = np.abs(A[tr]).std(0) + 1e-30
    W = np.linalg.solve((A[tr] / s).T @ (A[tr] / s) + np.eye(3) * 1e-9, (A[tr] / s).T @ t[tr])
    r = t[te] - (A[te] / s) @ W
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean())**2).sum()

def godard(X, w, iters=400):
    """minimize E(|Xw|^2 - 1)^2 over complex w, X real and whitened, by gradient with backtracking"""
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

def run(name, m, hm, ncomp=8):
    t1 = time.time()
    reg = Region(m)
    beta = coupling_mode(reg)
    f = F[m]
    mu = f.mean(0)
    C = (f - mu).T @ (f - mu) / len(f)
    ev, E = np.linalg.eigh(C)
    keep = ev > 1e-9 * ev.max()
    ev, E = ev[keep][::-1], E[:, keep][:, ::-1]
    Wh = E / np.sqrt(ev)                       # whitening: x = (f - mu) @ Wh
    X = (f - mu) @ Wh
    sb = SB[m]; ln = LN[m]
    targets = {"chi1(a0)": (np.exp(2j*np.pi*A0x[m]/10), A0x[m] >= 0), "chi1(a1)": (np.exp(2j*np.pi*A1x[m]/10), A1x[m] >= 0),
               "chi1(b1)": (np.exp(2j*np.pi*B1x[m]/10), B1x[m] >= 0)}
    print(f"{name}: cells {reg.n}, of them sums' B cells {int(sb.sum())}; whitened rank {X.shape[1]}; "
          f"the coupling mode's first-character alignment {character_of(beta)[1]:.2f} / {character_of(beta)[9]:.2f} (k=1 / k=9)", flush=True)
    def describe(label, a_state, j=None):
        z = (f - mu) @ a_state
        mod = np.abs(z)
        line = f"   {label}: modulus spread {mod.std() / mod.mean():.3f}" + (f", Godard cost {j:.4f}" if j is not None else "")
        line += "; at the sums' B cells " + ", ".join(f"{nm} {held(z[sb], t[sb], ok[sb], ln[sb]):.3f}" for nm, (t, ok) in targets.items())
        line += f"; held out with the coupling mode {read_heldout(a_state, beta, reg, hm)}, with chi_1 {read_heldout(a_state, chi(1, np.arange(10)), reg, hm)} of {int(SBh.sum())}"
        print(line, flush=True)
    found = []
    for q in range(ncomp):
        w0 = np.zeros(X.shape[1], dtype=complex); w0[2 * q] = 1; w0[2 * q + 1] = 1j
        P = np.array(found).T if found else None   # real columns already used (Re and Im of each read)
        Xq = X if P is None else X - (X @ P) @ np.linalg.pinv(P)
        w, j = godard(Xq, w0)
        if P is not None:
            w = w - P @ (np.linalg.pinv(P) @ w)
        found += [w.real, w.imag]
        describe(f"component {q + 1}", Wh @ w, j)
    # the outside read, scaled to its best constant modulus
    z = (f - mu) @ a_ideal
    s2 = (np.abs(z)**2).mean() / (np.abs(z)**4).mean()
    zz = z * np.sqrt(s2)
    describe("the outside read", a_ideal, ((np.abs(zz)**2 - 1)**2).mean())
    print(f"   {time.time() - t1:.1f} s", flush=True)

sec = np.floor((np.angle(H[:, 42] * np.conj(H[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
sech = np.floor((np.angle(Hh[:, 42] * np.conj(Hh[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
run("lock 42-35 sector 0", sec == 0, sech == 0)
run("the sums' B cells (label region)", SB, SBh)
print(f"done in {time.time() - t0:.1f} s")
