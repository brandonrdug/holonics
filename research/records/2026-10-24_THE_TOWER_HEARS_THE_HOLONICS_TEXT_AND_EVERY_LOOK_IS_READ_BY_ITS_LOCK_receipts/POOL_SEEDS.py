"""Each of the classes' coupling modes as a start for the blind pool.

POOL_SEED.py read the classes' coupling K over every arriving class (no digit set named): its two
leading modes sit on the lines' own marks (newline, the operations, `=`; the digits' power 0.000 and
0.094), and its third on the digits alone (0.999), turning with them as the first character of
their ring does (k=1 and k=9, 0.44 each). The machine's founding starts each rank from more than one
place and keeps the larger share (found-tower-situated: the unit and the ring start). Here every
one of K's four leading modes is a start of its own (a real pool, which the pool steps may turn),
beside the unit, and from each the form, the pool and the push gate are founded in turn (three
rounds) with the read on the landmark (after `=` on a sum's line). Each start prints its closing
share and step as BLIND_POOL.py; the pool law keeps the start with the largest share.
Projection: loading 45 s, K a few seconds, five starts of three rounds at about 22 s; about 380 s;
deadline 650 s; peak under 5 GiB. Uses POOL_SEED.py's loading (argument 1), then BLIND_POOL.py,
BLIND_GATE.py, OP_GATE.py, RING_REGIONS.py and FOUND_RING.py."""
import sys
ps = open(sys.argv[1]).read()
sys.argv = [sys.argv[0]] + sys.argv[2:]
exec(ps[:ps.index("bv = np.zeros(256, dtype=complex); bv[classes] = U[:, 0] + 1j * U[:, 1]")])
read = after_sum
starts = [("the unit", np.where(np.isin(np.arange(256), classes), 1.0, 0.0).astype(complex))]
for i in range(4):
    e = np.zeros(256, dtype=complex); e[classes] = U[:, i]
    starts.append((f"K's mode {i + 1}", e))
for name, bv in starts:
    print(f"from {name}: {pool_report(bv)}", flush=True)
    gv = np.ones(N)
    for rnd in range(3):
        P = a_cols(bv, gv)
        lead, th = found_k(*read_rows(P, read)); del P
        a = th[:128] + 1j * th[128:]
        P = b_cols(a, gv)
        lead, wv = found_k(*read_rows(P, read)); del P
        bv = np.zeros(256, dtype=complex); bv[classes] = wv[0::2] + 1j * wv[1::2]
        P = g_cols(a, bv)
        lead, gw = found_k(*read_rows(P, read)); del P
        gv = XG @ gw
    P = a_cols(bv, gv)
    lead, th = found_k(*read_rows(P, read)); del P
    a = th[:128] + 1j * th[128:]
    step(f"from {name}, closing", a, bv, gv, lead)
print(f"done in {time.time() - t0:.1f} s")
