# A count ruler (host arithmetic on public MNIST; a ruler, never machinery): what a pixel's code is, in nats a pixel,
# from mates on a line (the row-major strand, t +- k) and from mates on the helix (t +- 1 and t +- w, w the raster's width).
# Counts on training images 0..49999, read on 50000..50499 (the October 25 listener's held images); add-1/2 counts (KT).
import gzip, sys, numpy as np
raw = gzip.open(sys.argv[1], 'rb').read()
n, h, w = (int.from_bytes(raw[4 + 4 * i:8 + 4 * i], 'big') for i in range(3))
img = np.frombuffer(raw, dtype=np.uint8, offset=16).reshape(n, h * w)
train, held = img[:50000], img[50000:50500]
def code(levels, shift, offsets, both_dims):
    q = lambda a: (a >> shift).astype(np.int64)
    def contexts(a):
        a = q(a); m = a.shape[0]; ctx = np.zeros((m, h * w), dtype=np.int64)
        t = np.arange(h * w); r, c = t // w, t % w
        for (dr, dc, dt) in offsets:
            if both_dims:               # a mate on the raster: outside the raster reads the void (level 0)
                rr, cc = r + dr, c + dc; ok = (rr >= 0) & (rr < h) & (cc >= 0) & (cc < w); src = np.where(ok, rr * w + cc, 0)
            else:                       # a mate on the strand: t + dt, outside the strand reads the void
                tt = t + dt; ok = (tt >= 0) & (tt < h * w); src = np.where(ok, tt, 0)
            v = np.where(ok[None, :], a[:, src], 0)
            ctx = ctx * levels + v
        return ctx, a
    k = levels ** len(offsets)
    ctx, a = contexts(train)
    counts = np.bincount((ctx * levels + a).ravel(), minlength=k * levels).reshape(k, levels).astype(np.float64)
    ctx, a = contexts(held)
    num = counts[ctx.ravel(), a.ravel()] + 0.5; den = counts[ctx.ravel()].sum(axis=1) + 0.5 * levels
    return float(-np.log(num / den).mean()), k
L = lambda *ks: [(0, 0, k) for k in ks]                       # mates on the line
R = lambda *ps: [(dr, dc, 0) for dr, dc in ps]                # mates on the raster
print(f"MNIST {n} images of {h} by {w}; counts on 50,000, read on images 50000..50499 ({500 * h * w:,} pixels); nats a pixel")
for name, levels, shift in (("16 levels (the high digit of radix 16)", 16, 4), ("2 levels (128 and over)", 2, 7)):
    print(name)
    rows = [("no mate", L(), False),
            ("line: t-1", L(-1), False), ("helix: t-w (the mate one winding back)", R((-1, 0)), True),
            ("line: t-1, t-2", L(-1, -2), False), ("helix: t-1, t-w", R((0, -1), (-1, 0)), True),
            ("line: t-1 .. t-4", L(-1, -2, -3, -4), False), ("helix: t-1, t-w-1, t-w, t-w+1", R((0, -1), (-1, -1), (-1, 0), (-1, 1)), True),
            ("line, both sides: t-1, t+1", L(-1, 1), False), ("helix, both sides: t-1, t+1, t-w, t+w", R((0, -1), (0, 1), (-1, 0), (1, 0)), True)]
    if levels == 2:
        rows += [("line, both sides, the whole near field: t-5 .. t+5", L(-5, -4, -3, -2, -1, 1, 2, 3, 4, 5), False),
                 ("helix, both sides, the eight around", R((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)), True),
                 ("line, both sides, t-5 .. t+5 with t-w, t+w beside", [(0, 0, d) for d in (-5, -4, -3, -2, -1, 1, 2, 3, 4, 5)] + [(0, 0, -w), (0, 0, w)], False)]
    for label, offs, both in rows:
        c, k = code(levels, shift, offs, both)
        print(f"  {label:58s} {c:.4f}   ({k:,} contexts)")
