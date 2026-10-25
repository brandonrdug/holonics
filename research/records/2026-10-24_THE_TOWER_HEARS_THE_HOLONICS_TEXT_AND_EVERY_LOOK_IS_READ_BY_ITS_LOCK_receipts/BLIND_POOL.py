"""The pool founded blind beside the push gate, read on the received landmark.

BLIND_GATE.py founded the push gate blind with the read on the landmark (after `=` on a sum's line)
and read 393 of 495 held out at B, but its pool was the character chi_1 of the arriving digit,
handed to the ring: a table of the digits' values. The machine founds its class factor itself
(found-tower-situated's b over the arriving class). Here the pool is a complex factor over every
arriving class, founded blind by the same pool law, and the ring is pushed at every cell where the
pool is nonzero: push (a^T s_t) b_(u_t) (g^T x_t) into mode 41's moves, read on the landmark region
(the region's cells, centred within class, the region's own metric). From the unit pool (every
class alike) and the unit gate, the form a, the pool b and the push gate g are founded in turn,
four rounds. Each step prints the founded share, the pool's power on the digits and how it splits
over the characters of the digits' ring (an exterior read: the characters name the digits' values,
which the founding never sees), how much of "the second operand of a sum" the gate carries, how
much of chi_1(c0) the form holds at B and the held-out sums' units it reads there (through the
pool's digit values).
Projection: loading 40 s; a round about 35 s (the form's ring 10 s, the pool's 5 s, the gate's 6 s,
three foundings); four rounds about 180 s; deadline 400 s; peak under 5 GiB. Uses BLIND_GATE.py's
loading (argument 1, then OP_GATE.py, RING_REGIONS.py and FOUND_RING.py)."""
import sys
bg = open(sys.argv[1]).read()
sys.argv = [sys.argv[0], sys.argv[2], sys.argv[3], sys.argv[4]]
exec(bg[:bg.index("ones = np.ones(N)")])
Sall = X * 2**16
classes = np.unique(cls_all)
digits = np.arange(48, 58)
print(f"every cell's state on the pool's grain; classes present {len(classes)}", flush=True)

def pool_of(bv):
    """The pool's value at each cell (bv indexed by class)."""
    return bv[cls_all]

def a_cols(bv, gv):
    b = pool_of(bv) * gv
    V = np.zeros((N, 256), dtype=complex)
    V[:, :128] = b[:, None] * Sall; V[:, 128:] = 1j * b[:, None] * Sall
    return ring_of(V)

def b_cols(a, gv):
    v0 = (Sall @ a) * gv
    V = np.zeros((N, 2 * len(classes)), dtype=complex)
    for j, u in enumerate(classes):
        q = cls_all == u
        V[q, 2 * j] = v0[q]; V[q, 2 * j + 1] = 1j * v0[q]
    return ring_of(V)

def g_cols(a, bv):
    v = (Sall @ a) * pool_of(bv)
    return ring_of(v[:, None] * XG)

def pool_report(bv):
    d = bv[digits]
    on = (np.abs(d)**2).sum() / (np.abs(bv)**2).sum()
    k = np.arange(10)
    power = np.array([abs(np.vdot(chi(kk, k), d))**2 for kk in range(10)]) / (10 * (np.abs(d)**2).sum())
    return f"pool on the digits {on:.3f}, over the characters k=0..9 " + " ".join(f"{p:.2f}" for p in power)

def step(tag, a, bv, gv, lead):
    an = a / np.linalg.norm(a)
    d = bv[digits]
    print(f"   {tag}: share (circular) {lead:.4f}; {pool_report(bv)}; gate carries the second operand of a sum {carries(gv, dig_all, second):.3f}; "
          f"holds chi_1(c0) at B {holds_c0(an, d):.3f}, held out units at B {heldout_b(an, d)} of {len(C0h)} ({time.time() - t0:.0f} s)", flush=True)

bv = np.zeros(256, dtype=complex); bv[classes] = 1
gv = np.ones(N)
read = after_sum
for rnd in range(4):
    P = a_cols(bv, gv)
    lead, th = found_k(*read_rows(P, read)); del P
    a = th[:128] + 1j * th[128:]
    step(f"round {rnd}, the form", a, bv, gv, lead)
    P = b_cols(a, gv)
    lead, w = found_k(*read_rows(P, read)); del P
    bv = np.zeros(256, dtype=complex); bv[classes] = w[0::2] + 1j * w[1::2]
    step(f"round {rnd}, the pool", a, bv, gv, lead)
    P = g_cols(a, bv)
    lead, gw = found_k(*read_rows(P, read)); del P
    gv = XG @ gw
    step(f"round {rnd}, the push gate", a, bv, gv, lead)
print(f"done in {time.time() - t0:.1f} s")
