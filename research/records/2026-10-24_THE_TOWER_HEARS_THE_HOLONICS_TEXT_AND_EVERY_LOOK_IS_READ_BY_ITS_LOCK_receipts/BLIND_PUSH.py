"""The push gate founded blind, read where no operation is named.

BLIND_GATE.py: with the read on the label region (after `=` on a sum's line), the push gate founded
blind from a unit gate carries more of "the second operand of a sum" each round (0.34 to 0.55) and
the form reads 273, 371, 391, 393 of 495 held out at B. The read gate founded blind finds no
operation (0.02 to 0.05) and the form falls (247 to 186); both blind, 52 to 74. A push gate that
carries the operation leaves the ring near zero on other operations' lines (mode 41 keeps 0.80 a
cell), so the read may not need the operation. Here the push gate is founded blind, six rounds, with
the read after `=` on every line (the relation's arrival, no operation: a ceiling of what a lock
region can give, not the lock's own placing) and with the read at every cell (no region).
Projection: loading 40 s, about 15 s a round, two runs of six rounds; about 220 s, deadline 400 s,
peak under 5 GiB. Uses BLIND_GATE.py's functions (argument 1; then OP_GATE.py, RING_REGIONS.py and
FOUND_RING.py)."""
import sys
bg = open(sys.argv[1]).read()
sys.argv = [sys.argv[0], sys.argv[2], sys.argv[3], sys.argv[4]]
exec(bg[:bg.index("ones = np.ones(N)")])
after_all = []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    a_ = np.zeros(len(text), dtype=bool); start = 0
    for line in text.split(b"\n"):
        e = line.find(b"=")
        if e >= 0:
            a_[start + e:start + len(line)] = True
        start += len(line) + 1
    after_all.append(a_[128:len(text) - 1])
after_all = np.concatenate(after_all)
print(f"after = on every line: {after_all.sum()} cells (the sums' U cells among them {(after_all & read_u).sum()})", flush=True)
for run, read in [("read after = on every line", after_all), ("read at every cell", np.ones(N, dtype=bool))]:
    print(f"the push gate blind, {run}", flush=True)
    gv = np.ones(N)
    for rnd in range(6):
        P = a_columns(gv)
        lead, th = found_k(*read_rows(P, read))
        del P
        a = th[:128] + 1j * th[128:]
        report(f"round {rnd}, the form", a, gv, after_sum.astype(float), lead)
        Pg = g_columns(a)
        lead, gw = found_k(*read_rows(Pg, read))
        del Pg
        gv = XG @ gw
        report(f"round {rnd}, the push gate", a, gv, after_sum.astype(float), lead)
print(f"done in {time.time() - t0:.1f} s")
