"""A reading region the lock could give: the cells after a line's written relation.

RING_REGIONS.py: read only at the sums' U cells, the founded ring form holds 0.777 of chi_1(c0) at
B; read at every cell, 0.019. RING_TENSION_READ.py: the cells where the tension stands out hold
almost none of the U cells (162 of 8,986 in the top 20%). The lock where a located key fires puts
a digit line's moment on its `=` in 535 of 957 lines. Here the ring (mode 41, pool chi_1, pushed at
every digit arrival) is read at the cells after a line's `=` up to its end, `=` declared (a ceiling
of what a lock region can give, not the lock's own placing), for every operation; and, as the
narrower ceiling, after `=` on the lines whose operation is `+`. Uses RING_REGIONS.py (argument 1,
which loads FOUND_RING.py, argument 2)."""
import sys
rr = open(sys.argv[1]).read()
exec(rr[:rr.index("th_out = ")].replace("src = open(sys.argv[1]).read()", "src = open(sys.argv[2]).read()").replace('sys.argv = [sys.argv[1], "41", "chi1"]', 'sys.argv = [sys.argv[2], "41", "chi1"]'))
after, after_sum = [], []
for c in range(8):
    text = open(f"modes/block{c}.txt", "rb").read()
    a = np.zeros(len(text), dtype=bool); s = np.zeros(len(text), dtype=bool)
    start = 0
    for line in text.split(b"\n"):
        e = line.find(b"=")
        if e >= 0:
            a[start + e:start + len(line)] = True
            if b"+" in line[:e]:
                s[start + e:start + len(line)] = True
        start += len(line) + 1
    after.append(a[128:len(text) - 1]); after_sum.append(s[128:len(text) - 1])
after, after_sum = np.concatenate(after), np.concatenate(after_sum)
P = columns(np.ones(N, dtype=bool))
for name, read in [("after every line's =", after), ("after = on the sums' lines", after_sum)]:
    t1 = time.time()
    Q, yr, Yri = regional(P, read)
    lead, th = found_in(Q, yr, Yri)
    a = th[:128] + 1j * th[128:]
    print(f"read {name} ({read.sum()} cells, of them sums' U cells {(read & read_u).sum()} of {read_u.sum()}): the founded form's share {share_of(Q, yr, Yri, th):.4f}, "
          f"holds chi_1(c0) at B {holds_c0(a, beta):.3f}, held out units at B {heldout_b(a, beta)} of {len(C0h)} ({time.time() - t1:.1f} s)", flush=True)
print(f"done in {time.time() - t0:.1f} s")
