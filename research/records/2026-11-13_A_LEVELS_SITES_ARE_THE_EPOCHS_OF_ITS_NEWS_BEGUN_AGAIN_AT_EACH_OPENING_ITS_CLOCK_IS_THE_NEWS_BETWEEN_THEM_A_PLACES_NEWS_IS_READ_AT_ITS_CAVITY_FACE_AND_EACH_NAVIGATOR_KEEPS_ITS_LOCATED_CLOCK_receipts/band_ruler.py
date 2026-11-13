"""band_ruler: whether a speech passage's law is the same along the octave ladder, and whether a change of clock is a shift
of rung (G130). A host instrument: a count's code on public speech, never the machine's face; it enters no law.

The raster (rungs.c): rung s holds y_s, gaining (x - y_s) >> s at each sample (y_0 the sample); band s is y_s - y_(s+1), read
at a stride of 2^s samples, s = 0..6. A reader: the best of the four polynomial predictors on the count utterances; of its
residual e the counted part is a class given a context, the rest of e (its bits under the leading one) is flat.
  absolute   class = (bit length of e, sign), context = the last step's bit length
  gain-free  class = (bit length of e less the last step's, clipped to 8 either way, sign), context = the last two steps'
             difference of bit lengths, clipped to 4 either way
Ratios are of counted parts on the read utterances; `whole` beside a ratio adds the change of the flat part when the two
readers' predictors differ: (cross total - own total) / own counted + 1.

usage: python3 -I band_ruler.py RAW_DIR BANDS_DIR COUNT_UTTERANCES      Output: numbers only.
"""
import os
import sys

import numpy as np

raw, bands, n_count = sys.argv[1], sys.argv[2], int(sys.argv[3])
names = sorted(os.listdir(os.path.join(raw, "orig")))
LN2 = float(np.log(2.0))


def bl(x):
    return np.where(x == 0, 0, np.frexp(np.maximum(np.abs(x), 1).astype(np.float64))[1])


def parts(v, order, free):
    e = v.copy()
    for _ in range(order):
        e = np.concatenate([[0], np.diff(e)])
    e = e[4:]
    step = np.concatenate([[0], np.diff(v)])
    last, before = bl(step[3:-1]), bl(step[2:-2])
    b = bl(e)
    sign = (e < 0).astype(np.int64)
    if free:
        return np.clip(last - before, -4, 4) + 4, (np.clip(b - last, -8, 8) + 8) * 2 + sign, np.maximum(b - 1, 0)
    return last, b * 2 + sign, np.maximum(b - 1, 0)


class Reader:
    def __init__(self, seqs, free):
        self.free, best = free, None
        for order in range(4):
            c, k, r = (np.concatenate(z) for z in zip(*[parts(v, order, free) for v in seqs if len(v) > 8]))
            tab = np.zeros((48, 96))
            np.add.at(tab, (c, k), 1.0)
            p = (tab + 0.5) / (tab.sum(axis=1, keepdims=True) + 0.5 * 96)
            total = float(-np.log(p[c, k]).sum() + r.sum() * LN2)
            if best is None or total < best[0]:
                best = (total, order, p)
        _, self.order, self.p = best

    def read(self, seqs):
        counted = flat = 0.0
        n = 0
        for v in seqs:
            if len(v) <= 8:
                continue
            c, k, r = parts(v, self.order, self.free)
            counted += float(-np.log(self.p[c, k]).sum())
            flat += float(r.sum() * LN2)
            n += len(k)
        return counted, flat, n


def cross(tag, other, own, seqs):
    oc, of, n = own.read(seqs)
    xc, xf, _ = other.read(seqs)
    print("  %-58s counted=%.4f whole=%.4f | own: order=%d counted a place=%.4f flat=%.4f; other: order=%d counted=%.4f flat=%.4f; places=%d" % (
        tag, xc / oc, (xc + xf - oc - of) / oc + 1, own.order, oc / n, of / n, other.order, xc / n, xf / n, n))
    return xc / oc


def stream(kind):
    return [np.fromfile(os.path.join(raw, kind, n), dtype="<i2").astype(np.int64) for n in names]


def band(kind, s):
    return [np.fromfile(os.path.join(bands, kind, "%s.b%d" % (n[:-4], s)), dtype="<i4").astype(np.int64) for n in names]


C, R = slice(0, n_count), slice(n_count, len(names))
so, sf = stream("orig"), stream("fast")
print("BANDS utterances=%d count=%d read=%d" % (len(names), n_count, len(names) - n_count))
print("A the sample stream, absolute words")
a1 = cross("double speed by the original's reader over its own", Reader(so[C], False), Reader(sf[C], False), sf[R])
a2 = cross("the original by the double speed's reader over its own", Reader(sf[C], False), Reader(so[C], False), so[R])
print("A double speed by the original's reader=%.4f | the original by the double speed's reader=%.4f" % (a1, a2))

bo = {s: band("orig", s) for s in range(7)}
bf = {s: band("fast", s) for s in range(7)}
for free in (False, True):
    word = "gain-free" if free else "absolute"
    ro = {s: Reader(bo[s][C], free) for s in range(7)}
    rf = {s: Reader(bf[s][C], free) for s in range(7)}
    print("LADDER %s words: a band's own reading at the original's speed, then at double speed" % word)
    for kind, bs, rs in (("orig", bo, ro), ("fast", bf, rf)):
        for s in range(7):
            c, f, n = rs[s].read(bs[s][R])
            print("  BAND %s s=%d order=%d places=%8d counted a place=%.4f flat=%.4f nats=%.0f" % (kind, s, rs[s].order, n, c / n, f / n, c + f))
    print("B %s: band s+1 read by band s's reader over by its own, the original's speed" % word)
    b = [cross("band %d by band %d's reader" % (s + 1, s), ro[s], ro[s + 1], bo[s + 1][R]) for s in range(1, 6)]
    print("B %s mean of the five=%.4f largest=%.4f" % (word, float(np.mean(b)), max(b)))
    if not free:
        print("C the shift of rung, absolute words: the double-speed copy's band s-1")
        c1 = [cross("fast band %d by the original's band %d reader" % (s - 1, s), ro[s], rf[s - 1], bf[s - 1][R]) for s in range(2, 7)]
        c2 = [cross("fast band %d by the original's band %d reader" % (s - 1, s - 1), ro[s - 1], rf[s - 1], bf[s - 1][R]) for s in range(2, 7)]
        print("C shifted rung mean=%.4f largest=%.4f | the same rung mean=%.4f largest=%.4f" % (float(np.mean(c1)), max(c1), float(np.mean(c2)), max(c2)))
    else:
        c1 = [cross("fast band %d by the original's band %d reader" % (s - 1, s), ro[s], rf[s - 1], bf[s - 1][R]) for s in range(2, 7)]
        c2 = [cross("fast band %d by the original's band %d reader" % (s - 1, s - 1), ro[s - 1], rf[s - 1], bf[s - 1][R]) for s in range(2, 7)]
        print("(for information) gain-free: shifted rung mean=%.4f | the same rung mean=%.4f" % (float(np.mean(c1)), float(np.mean(c2))))
