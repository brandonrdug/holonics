"""Plural ranks with the pool founded blind, read on the received landmark.

BLIND_POOL.py: with the pool free over every arriving class, the founding read on the landmark
(after `=` on a sum's line) leads with the digits' common push (the pool's power on the characters
of the digits' ring sits at k=0, 0.98 to 1.00) and its share (circular 0.41) passes the chi_1 form's
(0.31, BLIND_GATE.py): a louder form than the crossing leads, so one form cannot be the sum's. Here
the founding is ranked as the machine founds ranks: each rank founds its form, pool and push gate
in turn from the unit pool and the unit gate (three rounds), and the tension at the landmark's cells
is deflated by the rank's two channels before the next rank (as PLURAL_RANKS.py). Each rank prints
its share, its pool's power on the digits and over the characters (exterior reads), how much of
"the second operand of a sum" its gate carries, how much of chi_1(c0) its form holds at B and the
held-out sums' units it reads there.
Projection: loading 45 s; a round about 22 s (BLIND_POOL.py's rounds took 20 s); three ranks of
three rounds and a closing form each, about 280 s; deadline 500 s; peak under 5 GiB. Uses
BLIND_POOL.py (argument 1), then BLIND_GATE.py, OP_GATE.py, RING_REGIONS.py and FOUND_RING.py."""
import sys
bp = open(sys.argv[1]).read()
sys.argv = [sys.argv[0]] + sys.argv[2:]
exec(bp[:bp.index("bv = np.zeros(256, dtype=complex); bv[classes] = 1\ngv = np.ones(N)")])
read = after_sum
for rank in range(3):
    bv = np.zeros(256, dtype=complex); bv[classes] = 1
    gv = np.ones(N)
    for rnd in range(3):
        P = a_cols(bv, gv)
        lead, th = found_k(*read_rows(P, read)); del P
        a = th[:128] + 1j * th[128:]
        P = b_cols(a, gv)
        lead, w = found_k(*read_rows(P, read)); del P
        bv = np.zeros(256, dtype=complex); bv[classes] = w[0::2] + 1j * w[1::2]
        P = g_cols(a, bv)
        lead, gw = found_k(*read_rows(P, read)); del P
        gv = XG @ gw
    P = a_cols(bv, gv)
    lead, th = found_k(*read_rows(P, read))
    a = th[:128] + 1j * th[128:]
    step(f"rank {rank}", a, bv, gv, lead)
    rows = np.nonzero(read)[0]
    Cr = np.stack([P[rows, 0] @ th, P[rows, 1] @ th], 1)
    del P
    for u in np.unique(cls_all[rows]):
        q = cls_all[rows] == u
        Cr[q] -= Cr[q].mean(0)
    yr = y_all[rows]
    y_all = y_all.copy()
    y_all[rows] = yr - Cr @ np.linalg.lstsq(Cr, yr, rcond=None)[0]
print(f"done in {time.time() - t0:.1f} s")
