# Host ruler (never machinery; floats, analysis only): how much of the three-body part of the law across a place a sum of R
# complex trilinear terms holds. Q(x|L,R) ~ exp(a(L,x) + b(x,R) + sum_j Re(u_j(L) w_j(x) v_j(R))): the pair tables of cap_g.py
# plus R triads, each a left context's, a letter's and a right context's complex reading multiplied (rank one in the three),
# all fitted together by conditional likelihood on TRAIN from cap_g.py's start (the count tables) and with its schedule (full
# batch, Adam), read on HELD128 at the contexts seen in TRAIN, the best held step taken (which favours the reader). At R = 0 it
# is cap_g.py, line for line: that run is the ruler's own reproduction. Against the joint table (0.576 nats at two letters each
# side) and the pair reader (1.030) it reads the share of the three-body part that R triads hold, which sizes a founding of
# triads (the leaky grip record 2.3 and 4.3: growth is sized from the part that is lacking). The triads' factors start at a
# fixed draw (RandomState(R)), so a read repeats. Usage: cap_t.py K R [seconds]  (K letters each side, R triads).
# CAP_CODEC names the codec when yard.py's own path is gone; train.npz is written from TRAIN.txt when absent (both private).
import numpy as np, time, sys, os
SYNTH = os.environ.get('CAP_T_SYNTH')  # a control on drawn data (no passage), for the ruler's own check
if SYNTH:
    rng = np.random.RandomState(7); A = 8; B = 9
    def drawn(n):
        L = rng.randint(0, 6, n); R = rng.randint(0, 6, n)
        x = (L + R) % A                     # a three-body law: parity-like, no pair reads it
        flip = rng.rand(n) < 0.2; x[flip] = rng.randint(0, A, flip.sum())
        return L, R, x
    LT, RT, xT = drawn(20000); LH, RH, xH = drawn(4000)
    uL, iL = np.unique(LT, return_inverse=True); uR, iR = np.unique(RT, return_inverse=True)
    cLh, cRh = LH, RH; t0 = time.time(); K = 1
else:
    yard = open('yard.py').read().split("xT,sT=load")[0]
    if os.environ.get('CAP_CODEC'):
        yard = '\n'.join("C=os.environ['CAP_CODEC']" if l.startswith('C=') else l for l in yard.split('\n'))
    exec(yard)
    if not os.path.exists('train.npz'):
        xT, sT = load('TRAIN.txt'); np.savez('train.npz', x=xT, seg=sT)
    z = np.load('train.npz'); xT = z['x'].astype(np.int64); sT = z['seg']; xH, sH = load('HELD128.txt'); t0 = time.time(); A = 100
    K = int(sys.argv[1])
    oL = tuple(range(-K, 0)); oR = tuple(range(1, K + 1))
    uL, iL = np.unique(ctx(xT, sT, oL), return_inverse=True); uR, iR = np.unique(ctx(xT, sT, oR), return_inverse=True)
    cLh = ctx(xH, sH, oL); cRh = ctx(xH, sH, oR)
R = int(sys.argv[2]); BUD = float(sys.argv[3]) if len(sys.argv) > 3 else 600
nL, nR = len(uL), len(uR)
uk, ik = np.unique(iL.astype(np.int64) * nR + iR, return_inverse=True); nk = len(uk); Lc = uk // nR; Rc = uk % nR
uc, nc = np.unique(ik * A + xT, return_counts=True); cnt = np.zeros((nk, A), np.float32); cnt[uc // A, uc % A] = nc; n = cnt.sum(1); N = float(n.sum())
del iL, iR, ik, uc, nc
def agg(idx, m):
    o = np.argsort(idx, kind='stable'); st = np.searchsorted(idx[o], np.arange(m)); return lambda G: np.add.reduceat(G[o], st, axis=0)
aL = agg(Lc, nL); aR = agg(Rc, nR)
uni = np.bincount(xT, minlength=B).astype(np.float64)[:A] + 0.5; uni /= uni.sum()
cl = aL(cnt); cr = aR(cnt)
a = np.log((cl + 0.5) / (cl.sum(1, keepdims=True) + 0.5 * A)).astype(np.float32)
b = (np.log((cr + 0.5) / (cr.sum(1, keepdims=True) + 0.5 * A)) - np.log(uni)[None, :]).astype(np.float32)
del cl, cr; start = 'the count tables'
rs = np.random.RandomState(R); s0 = 0.1
U = (s0 * (rs.randn(nL, R) + 1j * rs.randn(nL, R))).astype(np.complex64)
V = (s0 * (rs.randn(nR, R) + 1j * rs.randn(nR, R))).astype(np.complex64)
W = (s0 * (rs.randn(A, R) + 1j * rs.randn(A, R))).astype(np.complex64)
P_ = [a, b, U, V, W]; M_ = [np.zeros_like(p) for p in P_]; S_ = [np.zeros(p.shape, np.float32) for p in P_]
jL = np.searchsorted(uL, cLh); jL[jL >= nL] = 0; jR = np.searchsorted(uR, cRh); jR[jR >= nR] = 0
seen = (uL[jL] == cLh) & (uR[jR] == cRh); IH = np.arange(len(xH))
def logits(Li, Ri):
    return a[Li].astype(np.float64) + b[Ri] + ((U[Li] * V[Ri]) @ W.T).real
def held():
    Z = logits(jL, jR); Z -= Z.max(1, keepdims=True); lp = Z[IH, xH] - np.log(np.exp(Z).sum(1))
    return -lp[seen].mean(), seen.mean()
def grads():
    P = U[Lc] * V[Rc]
    Z = (a[Lc] + b[Rc] + (P @ W.T).real).astype(np.float32); Z -= Z.max(1, keepdims=True); np.exp(Z, out=Z); Z /= Z.sum(1, keepdims=True)
    loss = -float((cnt * np.log(np.maximum(Z, 1e-30))).sum()) / N
    Z *= n[:, None]; Z -= cnt; Z /= N            # dloss/dlogit
    gP = Z @ np.conj(W)                          # the complex gradient d/dRe + i d/dIm of Re(P W^T) weighed by Z
    return loss, [aL(Z), aR(Z), aL(np.conj(V[Rc]) * gP), aR(np.conj(U[Lc]) * gP), (Z.T @ np.conj(P)).astype(np.complex64)]
print('K=%d R=%d left contexts %d right contexts %d joint contexts %d; pair tables from %s  %.0fs' % (K, R, nL, nR, nk, start, time.time() - t0), flush=True)
h, sh = held(); print('  step   0  HELD128 (seen contexts, share %.4f) %.4f' % (sh, h), flush=True)
step = 0; best = (h, 0)
while time.time() - t0 < BUD:
    loss, G = grads(); step += 1; lr = 0.1 if step <= 40 else (0.03 if step <= 120 else 0.01); al = lr * np.sqrt(1 - 0.999 ** step) / (1 - 0.9 ** step)
    for p, g, m, s in zip(P_, G, M_, S_):
        m *= 0.9; m += 0.1 * g; s *= 0.999; s += (0.001 * np.abs(g) ** 2 if np.iscomplexobj(g) else 0.001 * g * g)  # cap_g.py's order
        p -= (al * m / (np.sqrt(s) + 1e-12)).astype(p.dtype)
    if step % 5 == 0 or step == 1:
        h, sh = held(); best = min(best, (h, step))
        print('  step %3d  TRAIN %.4f  HELD128 (seen contexts, share %.4f) %.4f   %.0fs' % (step, loss, sh, h, time.time() - t0), flush=True)
print('K=%d R=%d best HELD128 %.4f at step %d of %d' % (K, R, best[0], best[1], step))
