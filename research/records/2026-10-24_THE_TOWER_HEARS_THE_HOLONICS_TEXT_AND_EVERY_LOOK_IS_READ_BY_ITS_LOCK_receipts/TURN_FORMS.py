"""Turns and boosts at the second operand's arrival. A situated form c = (a^T s)(beta_d) acts on the
state's read by the arriving digit's factor beta_d. A factor of unit modulus turns that read (an
elliptic move); a real factor scales it (a boost, or a half-turn and a boost). Uses the loading,
the region and the search of REGION_SHARE.py (argument 1; its reports are not run).

(1) What the leading unconstrained form of a region reads, at the training sums' B cells: the
    straight-line fit of the result's size (log10 of the result) and of the first operand's units
    character chi_1(a0) from its two channels (fraction of the variance held, fitted on the even
    lines and read on the odd).
(2) The leading turn form: the same search with every digit's factor held to unit modulus
    (|beta_d| = 1), its phases located by the search (for fixed a, beta <- phase(A beta) repeated;
    for fixed beta, a by the generalized eigenproblem). Reported from the label-free starts (unit,
    ring) and from the outside form's start: its share in the region's own unit, beta's alignment
    with the characters of the ring of ten (the largest over k, a character and its conjugate being
    one reading), and the sums' units read held out from its two channels (uncentred).
Regions: every digit arrival, the sums' B cells alone (label region), the lock 42-35 sector 0."""
import sys, time
src = open(sys.argv[1]).read()
exec(src[:src.index("def report")])

# the result's size at each training digit arrival that is a second operand's units arrival
size = np.full(len(F), np.nan)
k = 0
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    pos = {}
    start = 0
    for line in text.split(b"\n"):
        m_ = tm.tower_circuit.EQ.match(line)
        if m_:
            a_, op_, b_, c_ = m_.groups()
            pos[start + len(a_) + len(b_)] = int(c_)   # the cell where b0 arrives
        start += len(line) + 1
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            i = int(line.split()[1])
            if i in pos:
                size[k] = math.log10(max(pos[i], 1))
            k += 1
assert k == len(F)
LINE = np.zeros(len(F), int)
k = 0
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    lines = np.cumsum([0] + [1 if x == 10 else 0 for x in text])
    for line in open(f"char/block{c}_dcov.txt"):
        if line.startswith("FORMS "):
            LINE[k] = lines[int(line.split()[1])]; k += 1

def held_r2(X, t, m):
    """The fraction of t's variance a straight-line fit from X holds, fitted on even lines, read on odd."""
    tr, te = m & (LINE % 2 == 0), m & (LINE % 2 == 1)
    A = np.hstack([X, np.ones((len(X), 1))])
    s = np.abs(A[tr]).std(0) + 1e-30
    w = np.linalg.solve((A[tr] / s).T @ (A[tr] / s) + np.eye(A.shape[1]) * 1e-6, (A[tr] / s).T @ t[tr])
    r = t[te] - (A[te] / s) @ w
    return 1 - (np.abs(r)**2).sum() / (np.abs(t[te] - t[te].mean(0))**2).sum()

def share(reg, a, b):
    """The form's canonical share in the region; a form whose two faces are one reading keeps one."""
    c = (reg.fc @ a) * b[reg.d]
    C = np.stack([c.real, c.imag], 1)
    R, G = C.T @ reg.y, C.T @ C
    return np.trace(reg.Yi @ R.T @ np.linalg.pinv(G, rcond=2**-30) @ R)

def turn_search(reg, a, b, steps=300):
    b = np.where(np.abs(b) > 0, b / np.maximum(np.abs(b), 1e-300), 1).astype(complex)
    Bden = reg.S.sum(0).astype(complex)
    j = reg.J(a, b)
    for _ in range(steps):
        V = np.einsum("kpq,p->qk", reg.M, a)
        A = V.conj().T @ reg.Yi @ V
        for _ in range(200):
            nb = A @ b
            nb = np.where(np.abs(nb) > 0, nb / np.maximum(np.abs(nb), 1e-300), b)
            if np.abs(nb - b).max() < 1e-12:
                b = nb; break
            b = nb
        N = np.einsum("k,kpq->qp", b, reg.M)
        _, a = geneig_top(N.conj().T @ reg.Yi @ N, Bden)
        jn = reg.J(a, b)
        if jn - j <= 1e-10 * abs(j):
            return jn, a, b
        j = jn
    return j, a, b

def characters(beta):
    al = character_of(beta)
    k = int(np.argmax(al[1:])) + 1
    return k, al[k], al[0]

def run(name, m, hm):
    t1 = time.time()
    reg = Region(m)
    tr = SB & m
    print(f"{name}: cells {reg.n}, sums' B cells {int(tr.sum())}", flush=True)
    st = reg.starts()
    j, a, b = max((reg.search(*st[s]) for s in ("unit", "ring")), key=lambda t: t[0])
    c = (F @ a) * b[D]
    C = np.stack([c.real, c.imag], 1)
    k_, al, al0 = characters(b)
    print(f"   leading form: share {share(reg, a, b):.4f}, beta k=0 {al0:.2f}; at the sums' B cells its two channels hold "
          f"{held_r2(C, size, tr):.3f} of the result's size (log10) and {held_r2(C, np.stack([np.cos(2*np.pi*A0/10), np.sin(2*np.pi*A0/10)], 1), tr):.3f} of chi_1(a0)", flush=True)
    for sname in ("unit", "ring", "outside"):
        j, a, b = turn_search(reg, *st[sname])
        k_, al, al0 = characters(b)
        print(f"   turn form from {sname}: J {j:.4f}, share {share(reg, a, b):.4f}; beta nearest k={k_} ({al:.2f}; k=0 {al0:.2f}); "
              f"held out, sums' units at B {read_heldout(a, b, reg, hm)} of {int(SBh.sum())}", flush=True)
    print(f"   {time.time() - t1:.1f} s", flush=True)

run("every digit arrival", np.ones(len(F), bool), np.ones(len(Fh), bool))
run("the sums' B cells (label region)", SB, SBh)
sec = np.floor((np.angle(H[:, 42] * np.conj(H[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
sech = np.floor((np.angle(Hh[:, 42] * np.conj(Hh[:, 35])) + math.pi) / (2 * math.pi) * 16).astype(int) % 16
run("lock 42-35 sector 0", sec == 0, sech == 0)
print(f"done in {time.time() - t0:.1f} s")
