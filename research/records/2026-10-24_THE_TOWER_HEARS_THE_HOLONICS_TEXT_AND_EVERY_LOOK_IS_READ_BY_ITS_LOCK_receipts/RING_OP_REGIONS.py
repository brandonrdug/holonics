"""The ring's push and read crossed with the operation: the ceiling an operation-aware gate can give.

RING_REGIONS.py: pushed at the sums' B cells and read at their U cells (labels on both sides), the ring
form founded in mode 41 with pool chi_1 holds 0.945 of chi_1(c0) at B and reads 443 of 495 held out;
situating one side gives about 295, neither 52. RING_AFTER_RELATION.py: pushed at every digit
arrival, read after `=` on the sums' lines, 273. OP_TURN_AT_B.py: after `-` and `*` the state does
not carry a0's units along the sums' form, so the operation must cross the ring.

Here the operation is a label (a line whose last operator before `=` is `+`), and the positions are
the ones an operator's and a relation's arrival bound, which the machine's own strands could locate:
- push at the second operand's digits on the sums' lines (between the operator and `=`), or at every
  digit arrival on the sums' lines before `=`;
- read after `=` on the sums' lines, or at the sums' U cells.
Each region's ring form is founded as in RING_REGIONS.py (mode 41, pool chi_1) and read held out at
B. If the operation-crossed regions reach the bar (370), the gates are worth building from the
state's own operator strand. Projection: loading 28 s, each push's columns about 20 s, each reading
about 5 s; about 90 s in all, deadline 180 s, peak under 4 GiB. Uses RING_REGIONS.py (argument 1,
which loads FOUND_RING.py, argument 2)."""
import sys
rr = open(sys.argv[1]).read()
exec(rr[:rr.index("th_out = ")].replace("src = open(sys.argv[1]).read()", "src = open(sys.argv[2]).read()").replace('sys.argv = [sys.argv[1], "41", "chi1"]', 'sys.argv = [sys.argv[2], "41", "chi1"]'))
second, sumdig, after_sum = [], [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    p2 = np.zeros(len(text), dtype=bool); pd = np.zeros(len(text), dtype=bool); s = np.zeros(len(text), dtype=bool)
    start = 0
    for line in text.split(b"\n"):
        e = line.find(b"=")
        if e >= 0:
            ops = [line.rfind(o, 0, e) for o in (b"+", b"-", b"*")]
            o = max(ops)
            if o >= 0 and line[o:o + 1] == b"+":
                s[start + e:start + len(line)] = True
                for k in range(e):
                    if 48 <= line[k] <= 57:
                        pd[start + k] = True
                        if k > o:
                            p2[start + k] = True
        start += len(line) + 1
    second.append(p2[128:len(text) - 1]); sumdig.append(pd[128:len(text) - 1]); after_sum.append(s[128:len(text) - 1])
second, sumdig, after_sum = np.concatenate(second), np.concatenate(sumdig), np.concatenate(after_sum)
print(f"push cells: the second operand's digits on the sums' lines {second.sum()} (B cells among them {(second & push_b).sum()} of {push_b.sum()}), every digit on the sums' lines {sumdig.sum()}; "
      f"read cells: after = on the sums' lines {after_sum.sum()} (U cells among them {(after_sum & read_u).sum()} of {read_u.sum()})", flush=True)
for pname, push, reads in [("the second operand's digits", second, [("after = on the sums' lines", after_sum), ("the sums' U cells", read_u)]),
                           ("every digit on the sums' lines", sumdig, [("after = on the sums' lines", after_sum)])]:
    t1 = time.time()
    P = columns(push)
    print(f"   columns for {pname} in {time.time() - t1:.1f} s", flush=True)
    for rname, read in reads:
        t2 = time.time()
        Q, yr, Yri = regional(P, read)
        lead, th = found_in(Q, yr, Yri)
        a = th[:128] + 1j * th[128:]
        print(f"pushed at {pname}, read {rname}: the founded form's share {share_of(Q, yr, Yri, th):.4f} (circular {lead:.4f}), "
              f"holds chi_1(c0) at B {holds_c0(a, beta):.3f}, held out units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t2:.1f} s)", flush=True)
    del P
print(f"done in {time.time() - t0:.1f} s")
