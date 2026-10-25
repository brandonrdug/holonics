"""Plural gated ranks in an operation-free region: does one rank hold the sum's crossing?

GATED_PUSH_FREE_READ.py: after `=` on every line, the sum's crossing (the label regions' form)
scores a circular share of 0.112 while the blind founding there finds 0.127, so a louder form leads
and a single founded form cannot be the sum's. Here the founding is ranked, as the machine founds
ranks: in the region after `=` on every line (the relation's arrival, no operation named), each rank
is a ring form in mode 41 with pool chi_1 and its own push gate founded blind (three rounds from a
unit gate, as BLIND_PUSH.py), and the tension is deflated by each founded rank before the next (the
input covector at the region's cells less its straight-line projection on the rank's two
channels). Each rank prints its share, how much of "the second operand of a sum", "of a difference"
and "of a product" its push gate carries (exterior reads), how much of chi_1(c0) its form holds at B
and how many held-out sums' units it reads there. Projection: loading 40 s, about 25 s a round,
three ranks of three rounds; about 270 s, deadline 500 s, peak under 5 GiB. Uses BLIND_PUSH.py's
loading (argument 1, then BLIND_GATE.py, OP_GATE.py, RING_REGIONS.py, FOUND_RING.py)."""
import sys
bp = open(sys.argv[1]).read()
sys.argv = [sys.argv[0]] + sys.argv[2:]
exec(bp[:bp.index("for run, read in")])
labels = {}
for op, name in [(b"+", "sum"), (b"-", "difference"), (b"*", "product")]:
    m = []
    for c in range(8):
        text = open(f"modes/block{c}.txt", "rb").read()
        p2 = np.zeros(len(text), dtype=bool); start = 0
        for line in text.split(b"\n"):
            e = line.find(b"=")
            if e >= 0:
                o = max(line.rfind(x, 0, e) for x in (b"+", b"-", b"*"))
                if o >= 0 and line[o:o + 1] == op:
                    for k in range(o + 1, e):
                        if 48 <= line[k] <= 57:
                            p2[start + k] = True
            start += len(line) + 1
        m.append(p2[128:len(text) - 1])
    labels[name] = np.concatenate(m)
read = after_all
for rank in range(3):
    gv = np.ones(N)
    for rnd in range(3):
        P = a_columns(gv)
        lead_a, th = found_k(*read_rows(P, read))
        del P
        a = th[:128] + 1j * th[128:]
        Pg = g_columns(a)
        lead_g, gw = found_k(*read_rows(Pg, read))
        del Pg
        gv = XG @ gw
    P = a_columns(gv)
    lead, th = found_k(*read_rows(P, read))
    a = th[:128] + 1j * th[128:]
    carried = ", ".join(f"{k} {carries(gv, dig_all, v):.3f}" for k, v in labels.items())
    an = a / np.linalg.norm(a)
    print(f"rank {rank}: share (circular) {lead:.4f}; its push gate carries the second operand of a {carried}; holds chi_1(c0) at B {holds_c0(an, beta):.3f}, "
          f"held out units at B {heldout_b(an, beta)} of {len(C0h)} ({time.time() - t0:.0f} s)", flush=True)
    rows = np.nonzero(read)[0]
    Cr = np.stack([P[rows, 0] @ th, P[rows, 1] @ th], 1)
    for u in np.unique(cls_all[rows]):
        q = cls_all[rows] == u
        Cr[q] -= Cr[q].mean(0)
    del P
    yr = y_all[rows]
    y_all = y_all.copy()
    y_all[rows] = yr - Cr @ np.linalg.lstsq(Cr, yr, rcond=None)[0]
print(f"done in {time.time() - t0:.1f} s")
