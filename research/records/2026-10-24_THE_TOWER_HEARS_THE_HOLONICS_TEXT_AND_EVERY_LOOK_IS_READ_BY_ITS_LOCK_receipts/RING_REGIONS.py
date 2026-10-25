"""Which side of the units crossing the unlabeled founding loses: where the form is pushed, or
where its ring is read.

FOUND_RING.py founded placed forms with their readers over the whole digit block (every digit
arrival pushes, every cell reads) and found no units crossing: the chi_1 forms hold at most 0.09 of
chi_1(c0) at B and read 51 to 68 of 495 held out. The exterior founding that found it (471) pushed
at the sums' B cells alone and read at their U cells alone. Here the ring rides mode 41 and the pool
is chi_1, and the push and the read are each taken over every cell or over the label cells (B for
the push, U for the read), four regions:
- the share the outside form (char/ideal_quiet.txt: chi_1(a0)'s read of the state, times chi_1 of
  the arriving digit) takes in each;
- the form the pool law founds in each, how much of chi_1(c0) at B it holds and how many held-out
  sums' units it reads at B.
Uses FOUND_RING.py's loading (argument 1)."""
import sys
src = open(sys.argv[1]).read()
sys.argv = [sys.argv[1], "41", "chi1"]
exec(src[:src.index("for pool in POOLS:")])
M = 41
beta = chi(1, np.arange(10))
push_b, read_u = [], []
for c, (lam, bet, y, cls, S, dig) in enumerate(parts):
    text = open(f"modes/block{c}.txt", "rb").read()
    role, info = tm.probe_roles(text)
    pb = np.zeros(len(cls), dtype=bool)
    for j in np.nonzero(dig)[0]:
        r = role.get(j + 128 + 1, ()); f = info.get(j + 128 + 1)
        pb[j] = "B" in r and bool(f) and f[0] == "+"
    ru = np.zeros(len(cls), dtype=bool)
    for x in open(f"char/block{c}.usum128").read().split():
        ru[int(x) - 128] = True
    push_b.append(pb); read_u.append(ru)
push_b, read_u = np.concatenate(push_b), np.concatenate(read_u)
print(f"label cells: B pushes {push_b.sum()}, U reads {read_u.sum()}", flush=True)
line = open("char/ideal_quiet.txt").read().split("\n")[1]
fld = {k: v for k, v in (f.split("=", 1) for f in line.split()[2:])}
a_out = np.array([int(x) for x in fld["a"].split(",")], dtype=float) + 1j * np.array([int(x) for x in fld["ai"].split(",")], dtype=float)
a_out /= np.linalg.norm(a_out)

def columns(push):
    """The ring's channels as linear functions of theta, pushed only where `push` holds; not centred."""
    out, at = [], 0
    for lam, bet, y, cls, S, dig in parts:
        n = len(cls)
        P = np.zeros((n, 2, 256))
        b = np.zeros(n, dtype=complex); on = dig & push[at:at + n]; b[on] = beta[cls[on] - 48]
        Cr = np.concatenate([b.real[:, None] * S, -b.imag[:, None] * S], 1)
        Ci = np.concatenate([b.imag[:, None] * S, b.real[:, None] * S], 1)
        l, q = lam[:, M], bet[:, M]
        Mv = np.stack([np.stack([l.real + q.real, q.imag - l.imag], 1), np.stack([l.imag + q.imag, l.real - q.real], 1)], 1)
        cur = np.zeros((2, 256))
        for t in range(n):
            cur = Mv[t] @ cur
            cur[0] += Cr[t]; cur[1] += Ci[t]
            P[t] = cur
        out.append(P); at += n
    return np.concatenate(out)

def regional(P, read):
    Q = P[read].copy(); yr = y_all[read]; cr = cls_all[read]
    for u in np.unique(cr):
        q = cr == u
        Q[q] -= Q[q].mean(0)
    Yr = yr.T @ yr; Yri = np.linalg.inv(Yr)
    return Q, yr, Yri

def share_of(Q, yr, Yri, th):
    C = np.stack([Q[:, 0] @ th, Q[:, 1] @ th], 1)
    R, G = C.T @ yr, C.T @ C
    return np.trace(Yri @ R.T @ np.linalg.pinv(G) @ R)

def found_in(Q, yr, Yri):
    X0, X1 = yr.T @ Q[:, 0], yr.T @ Q[:, 1]
    A = X0.T @ Yri @ X0 + X1.T @ Yri @ X1
    B = Q[:, 0].T @ Q[:, 0] + Q[:, 1].T @ Q[:, 1]
    B = B + np.eye(256) * 1e-9 * np.trace(B) / 256
    L = np.linalg.cholesky(B)
    w, V = np.linalg.eigh(np.linalg.solve(L, np.linalg.solve(L, A).T))
    return w[-1], np.linalg.solve(L.T, V[:, -1])

th_out = np.concatenate([a_out.real, a_out.imag])
everywhere = np.ones(N, dtype=bool)
for pname, push in [("every digit arrival", everywhere), ("the sums' B cells", push_b)]:
    t1 = time.time()
    P = columns(push)
    for rname, read in [("every cell", everywhere), ("the sums' U cells", read_u)]:
        Q, yr, Yri = regional(P, read)
        lead, th = found_in(Q, yr, Yri)
        a = th[:128] + 1j * th[128:]
        print(f"pushed at {pname}, read at {rname}: the outside form's share {share_of(Q, yr, Yri, th_out):.4f}; the founded form's {share_of(Q, yr, Yri, th):.4f} "
              f"(circular {lead:.4f}), holds chi_1(c0) at B {holds_c0(a, beta):.3f}, held out units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t1:.1f} s)", flush=True)
print(f"done in {time.time() - t0:.1f} s")
