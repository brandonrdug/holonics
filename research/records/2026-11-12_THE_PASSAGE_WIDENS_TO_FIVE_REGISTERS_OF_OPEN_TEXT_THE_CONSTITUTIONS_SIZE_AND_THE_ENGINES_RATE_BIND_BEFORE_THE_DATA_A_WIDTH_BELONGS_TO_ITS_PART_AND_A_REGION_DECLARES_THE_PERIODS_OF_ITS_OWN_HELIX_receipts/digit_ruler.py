"""A count ruler (an instrument, never machinery): what one leading digit of a pixel's value holds, by its radix and its cut.

MNIST's training images (train-images-idx3-ubyte.gz): counts on images 0..49,999, read on 50,000..50,499 (392,000
pixels), nats a pixel, add-1/2 counts. A digit of radix b reads the value at b levels: by equal steps of the value
(`a * b // 256`), or by cuts located at the value's own equal masses over the nonzero values, zero kept as its own
level. Beside the code with no mate known, the code with the four mates on the raster known on both sides (t-1, t+1,
t-w, t+w). The fill is the code with no mate over the digit's register, ln b.
"""
import gzip, struct, sys
import numpy as np

path = sys.argv[1]
with gzip.open(path, "rb") as fh:
    magic, n, h, w = struct.unpack(">IIII", fh.read(16))
    images = np.frombuffer(fh.read(), dtype=np.uint8).reshape(n, h * w)
train, held = images[:50000], images[50000:50500]
t = np.arange(h * w)
r, c = t // w, t % w
MATES = [(0, -1), (0, 1), (-1, 0), (1, 0)]


def equal_steps(b):
    return lambda a: (a.astype(np.int64) * b) // 256


def located(b):
    nonzero = np.sort(train[train > 0].ravel())
    cuts = [nonzero[len(nonzero) * k // (b - 1)] for k in range(1, b - 1)]
    cuts = np.array(sorted(set(int(v) for v in cuts)), dtype=np.int64)
    return lambda a: np.where(a == 0, 0, 1 + np.searchsorted(cuts, a.astype(np.int64), side="right"))


def code(levels, quant, mates):
    def contexts(a):
        a = quant(a)
        ctx = np.zeros(a.shape, dtype=np.int64)
        for dr, dc in mates:
            rr, cc = r + dr, c + dc
            ok = (rr >= 0) & (rr < h) & (cc >= 0) & (cc < w)
            src = np.where(ok, rr * w + cc, 0)
            ctx = ctx * levels + np.where(ok[None, :], a[:, src], 0)
        return ctx, a
    k = levels ** len(mates)
    ctx, a = contexts(train)
    counts = np.bincount((ctx * levels + a).ravel(), minlength=k * levels).reshape(k, levels).astype(np.float64)
    ctx, a = contexts(held)
    num = counts[ctx.ravel(), a.ravel()] + 0.5
    den = counts[ctx.ravel()].sum(axis=1) + 0.5 * levels
    return float(-np.log(num / den).mean())


print("radix  cut          no mate  fill    four mates both sides")
for b in (2, 3, 4, 5, 6, 8, 16):
    for name, quant in (("equal steps", equal_steps(b)), ("located", located(b))):
        if b == 2 and name == "located":
            quant = lambda a: (a > 0).astype(np.int64)
        alone, both = code(b, quant, []), code(b, quant, MATES)
        print(f"{b:>5}  {name:<11}  {alone:.4f}   {alone / np.log(b):.3f}   {both:.4f}")

# The second register: the level of ink, where there is ink (counts on the training images' inked pixels, read on
# the held images' inked pixels, no mate known), at b levels cut at the ink's own equal masses.
ink, held_ink = train[train > 0], held[held > 0]
print(f"ink share: counted images {(train > 0).mean():.4f}, read images {(held > 0).mean():.4f}")
print("levels of ink  nats an inked pixel  fill")
for b in (2, 3, 4, 8):
    ordered = np.sort(ink)
    cuts = np.array(sorted(set(int(ordered[len(ordered) * k // b]) for k in range(1, b))), dtype=np.int64)
    rank = lambda a: np.searchsorted(cuts, a.astype(np.int64), side="right")
    counts = np.bincount(rank(ink), minlength=b).astype(np.float64)
    nats = float(-np.log((counts[rank(held_ink)] + 0.5) / (counts.sum() + 0.5 * b)).mean())
    print(f"{len(cuts) + 1:>13}  {nats:.4f}               {nats / np.log(len(cuts) + 1):.3f}")
