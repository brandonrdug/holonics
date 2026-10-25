"""The gates founded blind: does the pool law find the operation's strands itself?

OP_GATE.py: the state carries "the second operand of a sum" on a straight line almost exactly
(R^2 0.992 at the digit arrivals) and "after `=` on a sum's line" less cleanly (0.824 at every
cell); with those label-fitted gates the ring form founded in mode 41, pool chi_1, reads 359 to 392
of 495 held out at B. Here no gate is fitted to a label. Each gate is a pair contact of the ring
with the state's straight-line read x = (state before the move, 1):
- the push gate g: the ring is pushed with (a^T s_t) beta_d (g^T x_t) at every digit arrival;
- the read gate h: the ring's lift into the input is weighted by (h^T x_t) at every cell, so the
  form read at cell t is (h^T x_t) r_t, centred within the arriving class, against the input
  covector at every cell.
The form a, then g, then h are founded in turn by the pool law (the leading generalized eigenvector
of a block's demand against its own loudness), each from the others' current values, starting
from unit gates (which is the unlabeled founding that read 52). Three runs: g blind with the read on
the label region (after `=` on a sum's line), h blind with the push on the label region (the
second operand of a sum), and both blind. Each round prints the founded share, how much of each
label the founded gate's value carries (an exterior read, R^2 of a straight-line fit), how much of
chi_1(c0) the form holds at B and how many held-out sums' units it reads there.
Projection: loading 40 s; the first run about 25 s a round, the second about 10 s, the third about
35 s; four rounds each, about 330 s in all; deadline 600 s; peak under 5 GiB. Uses OP_GATE.py's
loading (argument 1, which takes RING_REGIONS.py and FOUND_RING.py as arguments 2 and 3)."""
import sys
og = open(sys.argv[1]).read()
sys.argv = [sys.argv[0], sys.argv[2], sys.argv[3]]
exec(og[:og.index("def gate(rows, label):")])
XG = np.concatenate([X, np.ones((N, 1))], 1)
Sd_all = np.concatenate([p[4] for p in parts])
digit_beta = np.zeros(N, dtype=complex); d_at = np.nonzero(dig_all)[0]
digit_beta[d_at] = beta[cls_all[d_at] - 48]

def ring_of(V):
    """Ring columns: V (N x k complex, zero where no digit arrives) pushed through mode M's moves; returns (N, 2, k)."""
    k = V.shape[1]; out, at = [], 0
    for lam, bet, y, cls, S, dig in parts:
        n = len(cls)
        P = np.zeros((n, 2, k))
        Vr, Vi = V[at:at + n].real, V[at:at + n].imag
        l, q = lam[:, M], bet[:, M]
        Mv = np.stack([np.stack([l.real + q.real, q.imag - l.imag], 1), np.stack([l.imag + q.imag, l.real - q.real], 1)], 1)
        cur = np.zeros((2, k))
        for t in range(n):
            cur = Mv[t] @ cur
            cur[0] += Vr[t]; cur[1] += Vi[t]
            P[t] = cur
        out.append(P); at += n
    return np.concatenate(out)

def a_columns(gv):
    """The ring's columns over theta = (Re a, Im a): push (a^T s) beta g."""
    b = digit_beta * gv
    V = np.zeros((N, 256), dtype=complex)
    V[:, :128] = b[:, None] * Sd_all; V[:, 128:] = 1j * b[:, None] * Sd_all
    return ring_of(V)

def g_columns(a):
    """The ring's columns over the push gate g (129 real): push (a^T s) beta (g^T x)."""
    v = (Sd_all @ a) * digit_beta
    return ring_of(v[:, None] * XG)

def read_rows(P, read):
    """The rows the founding meets: on a label region, the region's cells (centred within class,
    the region's own metric); with a read gate value h_t, h_t P_t at every cell (centred within
    class, every cell's metric)."""
    if read.dtype == bool:
        return regional(P, read)
    Q = P * read[:, None, None]
    for u in np.unique(cls_all):
        q = cls_all == u
        Q[q] -= Q[q].mean(0)
    return Q, y_all, Yi

def found_k(Q, yr, Yri):
    k = Q.shape[2]
    X0, X1 = yr.T @ Q[:, 0], yr.T @ Q[:, 1]
    A = X0.T @ Yri @ X0 + X1.T @ Yri @ X1
    B = Q[:, 0].T @ Q[:, 0] + Q[:, 1].T @ Q[:, 1]
    B = B + np.eye(k) * 1e-9 * np.trace(B) / k
    L = np.linalg.cholesky(B)
    w, V = np.linalg.eigh(np.linalg.solve(L, np.linalg.solve(L, A).T))
    return w[-1], np.linalg.solve(L.T, V[:, -1])

def carries(gv, rows, label):
    A = np.stack([gv[rows], np.ones(rows.sum())], 1)
    t = label[rows].astype(float)
    w = np.linalg.lstsq(A, t, rcond=None)[0]
    return 1 - ((A @ w - t)**2).sum() / ((t - t.mean())**2).sum()

def h_columns(r):
    """The read gate's columns over h (129 real): (h^T x_t) r_t."""
    return np.stack([XG * r.real[:, None], XG * r.imag[:, None]], 1)

def report(tag, a, gv, hv, lead):
    a = a / np.linalg.norm(a)
    print(f"   {tag}: share (circular) {lead:.4f}; push gate carries the second operand of a sum {carries(gv, dig_all, second):.3f}, "
          f"read gate carries after = on a sum's line {carries(hv, np.ones(N, dtype=bool), after_sum):.3f}; "
          f"holds chi_1(c0) at B {holds_c0(a, beta):.3f}, held out units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t0:.0f} s)", flush=True)

ones = np.ones(N)
for run, g_blind, h_blind in [("the push gate blind, read after = on a sum's line", True, False),
                              ("the read gate blind, pushed at a sum's second operand", False, True),
                              ("both gates blind", True, True)]:
    print(run, flush=True)
    gv = ones.copy() if g_blind else second.astype(float)
    hv = ones.copy() if h_blind else None
    read = hv if h_blind else after_sum
    Pa = None if g_blind else a_columns(gv)
    for rnd in range(4):
        P = a_columns(gv) if g_blind else Pa
        lead, th = found_k(*read_rows(P, read))
        a = th[:128] + 1j * th[128:]
        report(f"round {rnd}, the form", a, gv, hv if h_blind else after_sum.astype(float), lead)
        if g_blind:
            del P
            Pg = g_columns(a)
            lead, gw = found_k(*read_rows(Pg, read))
            del Pg
            gv = XG @ gw
            report(f"round {rnd}, the push gate", a, gv, hv if h_blind else after_sum.astype(float), lead)
        if h_blind:
            P = a_columns(gv) if g_blind else Pa
            r = P[:, 0] @ th + 1j * (P[:, 1] @ th)
            del P
            Ph = h_columns(r)
            lead, hw = found_k(*read_rows(Ph, np.ones(N)))
            del Ph
            hv = XG @ hw; read = hv
            report(f"round {rnd}, the read gate", a, gv, hv, lead)
print(f"done in {time.time() - t0:.1f} s")
