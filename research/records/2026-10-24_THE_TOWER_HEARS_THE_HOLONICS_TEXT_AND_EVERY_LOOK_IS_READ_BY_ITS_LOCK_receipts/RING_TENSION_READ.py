"""A reading region with no label: the cells where the tension stands out.

RING_REGIONS.py found the reading side decisive: pushed at every digit arrival and read only at the
sums' U cells, the founded form holds 0.777 of chi_1(c0) at B and reads 293 of 495 held out; read
at every cell, 0.019 and 52. Here the ring (mode 41, pool chi_1, pushed at every digit arrival) is
read at the cells whose input covector stands out in the tension's own metric (leverage
y Y^-1 y^T, Y over every cell), the top 2, 5, 10 and 20 percent: how many of the sums' U cells that
region holds, and what the founding finds there. Uses RING_REGIONS.py (argument 1, which loads
FOUND_RING.py, argument 2)."""
import sys
rr = open(sys.argv[1]).read()
exec(rr[:rr.index("th_out = ")].replace("src = open(sys.argv[1]).read()", "src = open(sys.argv[2]).read()").replace('sys.argv = [sys.argv[1], "41", "chi1"]', 'sys.argv = [sys.argv[2], "41", "chi1"]'))
lev = np.einsum("ij,jk,ik->i", y_all, Yi, y_all)
P = columns(np.ones(N, dtype=bool))
for q in (0.02, 0.05, 0.10, 0.20):
    t1 = time.time()
    read = lev >= np.quantile(lev, 1 - q)
    Q, yr, Yri = regional(P, read)
    lead, th = found_in(Q, yr, Yri)
    a = th[:128] + 1j * th[128:]
    kinds = np.bincount(cls_all[read], minlength=128)
    top = ", ".join(f"{chr(u) if 33 <= u < 127 else hex(u)} {kinds[u]}" for u in np.argsort(kinds)[::-1][:5])
    print(f"read at the top {q:.0%} by tension ({read.sum()} cells, of them sums' U cells {(read & read_u).sum()} of {read_u.sum()}; arriving classes {top}): "
          f"the founded form's share {share_of(Q, yr, Yri, th):.4f}, holds chi_1(c0) at B {holds_c0(a, beta):.3f}, held out units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t1:.1f} s)", flush=True)
print(f"done in {time.time() - t0:.1f} s")
