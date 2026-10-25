"""With the push gated by the operation, does the read still need it? And is the crossing the
loudest thing an operation-free region holds?

BLIND_PUSH.py: read after `=` on every line or at every cell, the push gate founded blind carries
none of "the second operand of a sum" (0.002 to 0.015) and the form reads 50 to 78 of 495 held out,
at founded circular shares 0.127 and 0.106. Here the push is gated by the label (the second operand
of a sum) and the form is founded with the read after `=` on every line, and at every cell: if it
holds the crossing, only the push needs the operation. Beside it, the form founded on the label
regions (pushed at the second operand of a sum, read after `=` on a sum's line) is scored in each
operation-free region: if its circular share there is below the blind founding's, the crossing is
not the loudest thing those regions hold, and the founding there selects something else.
Projection: loading 40 s, one push's columns 15 s, three foundings and two scorings a few seconds
each; about 75 s, deadline 180 s, peak under 5 GiB. Uses BLIND_PUSH.py's loading (argument 1, then
BLIND_GATE.py, OP_GATE.py, RING_REGIONS.py, FOUND_RING.py)."""
import sys
bp = open(sys.argv[1]).read()
sys.argv = [sys.argv[0]] + sys.argv[2:]
exec(bp[:bp.index("for run, read in")])

def circular(Q, yr, Yri, th):
    X0, X1 = yr.T @ (Q[:, 0] @ th), yr.T @ (Q[:, 1] @ th)
    num = X0 @ Yri @ X0 + X1 @ Yri @ X1
    den = (Q[:, 0] @ th) @ (Q[:, 0] @ th) + (Q[:, 1] @ th) @ (Q[:, 1] @ th)
    return num / den

P = a_columns(second.astype(float))
lead, th_lab = found_k(*read_rows(P, after_sum))
a = th_lab[:128] + 1j * th_lab[128:]
report("the label regions (pushed at a sum's second operand, read after = on a sum's line)", a, second.astype(float), after_sum.astype(float), lead)
for rname, read in [("after = on every line", after_all), ("every cell", np.ones(N, dtype=bool))]:
    Q, yr, Yri = read_rows(P, read)
    print(f"   that form scored read at {rname}: circular share {circular(Q, yr, Yri, th_lab):.4f}", flush=True)
    lead, th = found_k(Q, yr, Yri)
    a = th[:128] + 1j * th[128:]
    report(f"pushed at a sum's second operand, founded read at {rname}", a, second.astype(float), after_sum.astype(float), lead)
    del Q, yr
print(f"done in {time.time() - t0:.1f} s")
