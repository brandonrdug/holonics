"""Gates the state's own straight-line read could give the ring: the operation crossed softly.

RING_OP_REGIONS.py: pushed at the second operand's digits on the sums' lines and read after `=` on
those lines (regions an operator's and a relation's arrival bound, the operation a label), the ring
form founded in mode 41 with pool chi_1 reads 385 of 495 held out at B, past the bar (370). The
machine has no label: a gate it could found is a read of its own state. Here the state is level 0's
state before the move at every cell (char/block{c}_allstate.i64, read-tower-modes full, 128 real
coordinates on 2^-24), and each gate is the state's straight-line read (with a constant) fitted to
one label region: the push gate on the digit arrivals to "the second operand of a sum", the read gate
on every cell to "after `=` on a sum's line". This is a label fit, so it is a ceiling for a linear
strand, not a founding. The ring's push is weighted by the push gate's value (or its square) and its
reading cells by the read gate's (or its square), and the ring form is founded as in RING_REGIONS.py.
The sums' B cells' form is read held out at B unweighted. Projection: loading 30 s, the states 10 s,
three pushes' columns about 15 s each, the readings a few seconds each; about 120 s, deadline
300 s, peak under 5 GiB. Uses RING_REGIONS.py (argument 1, which loads FOUND_RING.py, argument 2)."""
import sys
rr = open(sys.argv[1]).read()
exec(rr[:rr.index("th_out = ")].replace("src = open(sys.argv[1]).read()", "src = open(sys.argv[2]).read()").replace('sys.argv = [sys.argv[1], "41", "chi1"]', 'sys.argv = [sys.argv[2], "41", "chi1"]'))
X, second, after_sum, dig_all = [], [], [], []
for c, (lam, bet, y, cls, S, dig) in enumerate(parts):
    st = np.fromfile(f"char/block{c}_allstate.i64", dtype=np.int64).reshape(-1, 2 + 128)
    if not np.array_equal(st[:, 0], np.arange(128, 128 + len(cls))):
        raise SystemExit(f"block{c}: the states are not every cell")
    X.append(st[:, 2:].astype(float) / 2**24)
    text = open(f"modes/block{c}.txt", "rb").read()
    p2 = np.zeros(len(text), dtype=bool); s = np.zeros(len(text), dtype=bool)
    start = 0
    for line in text.split(b"\n"):
        e = line.find(b"=")
        if e >= 0:
            o = max(line.rfind(op, 0, e) for op in (b"+", b"-", b"*"))
            if o >= 0 and line[o:o + 1] == b"+":
                s[start + e:start + len(line)] = True
                for k in range(o + 1, e):
                    if 48 <= line[k] <= 57:
                        p2[start + k] = True
        start += len(line) + 1
    second.append(p2[128:len(text) - 1]); after_sum.append(s[128:len(text) - 1]); dig_all.append(dig)
X, second, after_sum, dig_all = np.concatenate(X), np.concatenate(second), np.concatenate(after_sum), np.concatenate(dig_all)
Sd = np.concatenate([p[4] for p in parts])[dig_all]
cc = np.corrcoef(X[dig_all].ravel(), Sd.ravel())[0, 1]
print(f"states {X.shape}; at the digit arrivals the state before the move against the situated pool's state: correlation {cc:.4f}", flush=True)

def gate(rows, label):
    A = np.concatenate([X[rows], np.ones((rows.sum(), 1))], 1)
    w = np.linalg.lstsq(A, label[rows].astype(float), rcond=None)[0]
    g = np.concatenate([X, np.ones((N, 1))], 1) @ w
    t = label[rows]; r2 = 1 - ((g[rows] - t)**2).sum() / ((t - t.mean())**2).sum()
    return g, r2

g_push, r2p = gate(dig_all, second)
g_read, r2r = gate(np.ones(N, dtype=bool), after_sum)
print(f"push gate (digit arrivals, second operand of a sum): R^2 {r2p:.3f}; mean in region {g_push[dig_all & second].mean():.3f}, out {g_push[dig_all & ~second].mean():.3f}, at the sums' B cells {g_push[push_b].mean():.3f}", flush=True)
print(f"read gate (every cell, after = on a sum's line): R^2 {r2r:.3f}; mean in region {g_read[after_sum].mean():.3f}, out {g_read[~after_sum].mean():.3f}, at the sums' U cells {g_read[read_u].mean():.3f}", flush=True)

def columns_w(wt):
    out, at = [], 0
    for lam, bet, y, cls, S, dig in parts:
        n = len(cls)
        P = np.zeros((n, 2, 256))
        b = np.zeros(n, dtype=complex); b[dig] = beta[cls[dig] - 48] * wt[at:at + n][dig]
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

def regional_w(P, v):
    Q = P.copy(); yr = y_all * v[:, None]; v2 = v**2
    for u in np.unique(cls_all):
        q = cls_all == u
        if v2[q].sum() > 0:
            Q[q] -= np.tensordot(v2[q], P[q], 1) / v2[q].sum()
    Q *= v[:, None, None]
    Yr = yr.T @ yr
    return Q, yr, np.linalg.inv(Yr)

pushes = [("the label (second operand of a sum)", second.astype(float)), ("the push gate", g_push), ("the push gate squared", g_push**2)]
reads = [("the label (after = on a sum's line)", after_sum.astype(float)), ("the read gate", g_read), ("the read gate squared", g_read**2)]
for pname, pw in pushes:
    t1 = time.time()
    P = columns_w(pw)
    print(f"   columns for {pname} in {time.time() - t1:.1f} s", flush=True)
    for rname, rv in reads:
        if pname.startswith("the label") and rname.startswith("the label"):
            continue
        t2 = time.time()
        Q, yr, Yri = regional_w(P, rv)
        lead, th = found_in(Q, yr, Yri)
        a = th[:128] + 1j * th[128:]
        print(f"pushed by {pname}, read by {rname}: the founded form's share {share_of(Q, yr, Yri, th):.4f} (circular {lead:.4f}), "
              f"holds chi_1(c0) at B {holds_c0(a, beta):.3f}, held out units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t2:.1f} s)", flush=True)
        del Q, yr
    del P
print(f"done in {time.time() - t0:.1f} s")
