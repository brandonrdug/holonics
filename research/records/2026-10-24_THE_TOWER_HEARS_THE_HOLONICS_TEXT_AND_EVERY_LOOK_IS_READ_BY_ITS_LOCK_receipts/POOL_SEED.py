"""A start for the blind pool from the classes' own coupling.

BLIND_POOL.py and PLURAL_POOL.py: from the unit pool (every class alike) the pool founded blind
stays at the digits' common push (k=0, 0.98 to 1.00) at every round and in every rank: the unit is
a fixed point of the alternation, as the unit start was for the form before the machine's ring
start (found-tower-situated's ring_seed: "the unit start, every class alike, cancels it"). The
start a pool needs is one each class reads with its own phase. CLASS_MODES.py located it at the
digit arrivals: the classes' coupling through the tension, K_uv = tr(Y^-1 Mt_u^T Sbar^-1 Mt_v) /
sqrt(n_u n_v), after the common read (Mt_u the class's state-tension moment less the common read,
Sbar the common Gram per cell), has the characters of the digits' ring as its modes. Here K is read
over every arriving class at every cell (no digit set named), its leading pair of modes is the
complex pool start e1 + i e2, and the form, the pool and the push gate are founded in turn from it
and the unit gate (three rounds) with the read on the landmark (after `=` on a sum's line). Prints
K's leading eigenvalues, each leading mode's power on the digits and over the characters of the
digits' ring (exterior reads), then each step as BLIND_POOL.py.
Projection: loading 45 s, K a few seconds, three rounds about 22 s each; about 120 s; deadline
300 s; peak under 5 GiB. Uses BLIND_POOL.py (argument 1), then BLIND_GATE.py, OP_GATE.py,
RING_REGIONS.py and FOUND_RING.py."""
import sys
bp = open(sys.argv[1]).read()
sys.argv = [sys.argv[0]] + sys.argv[2:]
exec(bp[:bp.index("bv = np.zeros(256, dtype=complex); bv[classes] = 1\ngv = np.ones(N)")])
Ss, Ms, ns = [], [], []
for u in classes:
    q = cls_all == u
    Ss.append(Sall[q].T @ Sall[q]); Ms.append(Sall[q].T @ y_all[q]); ns.append(q.sum())
Ss, Ms, ns = np.array(Ss), np.array(Ms), np.array(ns, dtype=float)
S = Ss.sum(0)
Wbar = np.linalg.solve(S, Ms.sum(0))
Mt = Ms - np.einsum("kpq,qr->kpr", Ss, Wbar)
Sbar = S / N
Z = np.array([np.linalg.solve(Sbar, Mt[k]) for k in range(len(classes))])
Yi_all = np.linalg.inv(y_all.T @ y_all)
K = np.einsum("kpq,qr,lpr->kl", Mt, Yi_all, Z) / np.sqrt(np.outer(ns, ns))
K = (K + K.T) / 2
w, U = np.linalg.eigh(K)
w, U = w[::-1], U[:, ::-1]
print(f"K over {len(classes)} classes ({', '.join(chr(c) if 32 < c < 127 else hex(c) for c in classes)}): leading eigenvalues {', '.join(f'{x:.4f}' for x in w[:6])}", flush=True)
dpos = np.array([np.nonzero(classes == d)[0][0] for d in digits])
for i in range(4):
    e = np.zeros(256, dtype=complex); e[classes] = U[:, i]
    print(f"   mode {i + 1}: {pool_report(e)}", flush=True)
bv = np.zeros(256, dtype=complex); bv[classes] = U[:, 0] + 1j * U[:, 1]
print(f"the start (modes 1 + i 2): {pool_report(bv)}", flush=True)
gv = np.ones(N)
read = after_sum
for rnd in range(3):
    P = a_cols(bv, gv)
    lead, th = found_k(*read_rows(P, read)); del P
    a = th[:128] + 1j * th[128:]
    step(f"round {rnd}, the form", a, bv, gv, lead)
    P = b_cols(a, gv)
    lead, wv = found_k(*read_rows(P, read)); del P
    bv = np.zeros(256, dtype=complex); bv[classes] = wv[0::2] + 1j * wv[1::2]
    step(f"round {rnd}, the pool", a, bv, gv, lead)
    P = g_cols(a, bv)
    lead, gw = found_k(*read_rows(P, read)); del P
    gv = XG @ gw
    step(f"round {rnd}, the push gate", a, bv, gv, lead)
print(f"done in {time.time() - t0:.1f} s")
