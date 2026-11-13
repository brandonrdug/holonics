"""band_cut: the restarting cut on a band's places, and what of its openings a change of start, the shift of rung and a
ratio off the ladder keep (G133). A host instrument: a count's code on public speech, never the machine's face; it enters no law.

The raster is rungs_kept.c's (rung s keeps its sum on 2^-s; band s = rung s less rung s+1, read every 2^s samples), bands 2 to 6.
A band's reader is band_ruler.py's with absolute words (the best of four polynomial predictors on the count utterances; of its
residual the counted part is (bit length, sign) given the last step's bit length, the rest of the residual flat), fit on the
original's count utterances. A place's code two ways: whole (counted and flat) and counted alone.
The cut: an opening sets a to its place's code; a place opens where a plus its code passes the section, and then a is its code.
The odometer: a place opens where the running news passes a multiple of the section.
Sections: 16 bits on the whole code; and for each code the section located on the original (bisection) for a mean epoch of 2
places and of 6.
Changes, the copy read by the original's reader of the band named:
  i    the cut begun 7 places later on the same codes (openings past the 39th place compared)
  ii   the passage begun 37 samples later, the same band (places at the copy's q 2^s, the original's time q 2^s + 37)
  iii  the double-speed copy's band s-1 (the original's time 2 q 2^(s-1))
  iv   the copy at one and a half times the speed, its band s-1 (the original's time 1.5 q 2^(s-1))
An opening is kept where the copy opens within half the wider of the two strides, in the original's time. Chance: the copy's
openings moved 1,000 of its strides along, around the utterance. Lift: (kept - chance) / (1 - chance).

usage: python3 -I band_cut.py RAW_DIR BANDS_DIR COUNT_UTTERANCES      Output: numbers only.
"""
import os
import sys

import numpy as np

raw, bands, n_count = sys.argv[1], sys.argv[2], int(sys.argv[3])
names = sorted(os.listdir(os.path.join(raw, "orig")))
LN2 = float(np.log(2.0))
START, SHIFT, FAR = 7, 37, 1000


def bl(x):
    return np.where(x == 0, 0, np.frexp(np.maximum(np.abs(x), 1).astype(np.float64))[1])


def parts(v, order):
    e = v.copy()
    for _ in range(order):
        e = np.concatenate([[0], np.diff(e)])
    e = e[4:]
    step = np.concatenate([[0], np.diff(v)])
    last = bl(step[3:-1])
    b = bl(e)
    return last, b * 2 + (e < 0).astype(np.int64), np.maximum(b - 1, 0)


class Reader:
    def __init__(self, seqs):
        best = None
        for order in range(4):
            c, k, r = (np.concatenate(z) for z in zip(*[parts(v, order) for v in seqs if len(v) > 8]))
            tab = np.zeros((48, 96))
            np.add.at(tab, (c, k), 1.0)
            p = (tab + 0.5) / (tab.sum(axis=1, keepdims=True) + 0.5 * 96)
            total = float(-np.log(p[c, k]).sum() + r.sum() * LN2)
            if best is None or total < best[0]:
                best = (total, order, p)
        _, self.order, self.p = best

    def codes(self, v):
        """(counted, flat) a place, for the places 4 on."""
        c, k, r = parts(v, self.order)
        return -np.log(self.p[c, k]), r * LN2


def band(kind, s):
    return [np.fromfile(os.path.join(bands, kind, "%s.b%d" % (n[:-4], s)), dtype="<i4").astype(np.int64) for n in names]


def cut(c, sigma):
    c = c.tolist()
    out, a = [0], c[0]
    for t in range(1, len(c)):
        x = c[t]
        if a + x > sigma:
            out.append(t)
            a = x
        else:
            a += x
    return np.asarray(out, dtype=np.int64)


def odometer(c, sigma):
    q = np.floor(np.cumsum(c) / sigma).astype(np.int64)
    return np.concatenate([[0], np.nonzero(np.diff(q) > 0)[0] + 1])


def locate(seqs, law, target):
    lo, hi = 0.0, 4000.0
    places = sum(len(c) for c in seqs)
    for _ in range(26):
        mid = (lo + hi) / 2
        if places / sum(len(law(c, mid)) for c in seqs) < target:
            lo = mid
        else:
            hi = mid
    return hi


def near(times_a, times_b, tol):
    """How many of a's times have a time of b within tol."""
    if len(times_b) == 0 or len(times_a) == 0:
        return 0
    i = np.searchsorted(times_b, times_a)
    left = np.abs(times_a - times_b[np.clip(i - 1, 0, len(times_b) - 1)])
    right = np.abs(times_b[np.clip(i, 0, len(times_b) - 1)] - times_a)
    return int((np.minimum(left, right) <= tol).sum())


def ranks(x):
    order = np.argsort(x, kind="stable")
    r = np.empty(len(x))
    r[order] = np.arange(len(x), dtype=np.float64)
    xs = x[order]
    start = np.concatenate([[0], np.nonzero(np.diff(xs) != 0)[0] + 1, [len(x)]])
    for a, b in zip(start[:-1], start[1:]):
        r[order[a:b]] = (a + b - 1) / 2
    return r


def spearman(x, y):
    rx, ry = ranks(x), ranks(y)
    rx -= rx.mean()
    ry -= ry.mean()
    return float((rx * ry).sum() / np.sqrt((rx * rx).sum() * (ry * ry).sum()))


C, R = slice(0, n_count), slice(n_count, len(names))
print("CUT utterances=%d count=%d read=%d start=%d shift_samples=%d far_strides=%d" % (len(names), n_count, len(names) - n_count, START, SHIFT, FAR))
pooled = {}
for s in range(2, 7):
    o_all = band("orig", s)
    reader = Reader(o_all[C])
    stride = 1 << s
    # each version: (name, the copy's band values a read utterance, the copy's stride in the original's time, its offset there)
    versions = {
        "ii": (band("shift", s)[R], float(stride), float(SHIFT)),
        "iii": (band("fast", s - 1)[R], 2.0 * (stride >> 1), 0.0),
        "iv": (band("r150", s - 1)[R], 1.5 * (stride >> 1), 0.0),
    }
    own150 = Reader(band("r150", s - 1)[C])
    oc = [reader.codes(v) for v in o_all[R]]
    vc = {k: [reader.codes(v) for v in val[0]] for k, val in versions.items()}
    x150 = sum(float(reader.codes(v)[0].sum()) for v in versions["iv"][0]) / sum(float(own150.codes(v)[0].sum()) for v in versions["iv"][0])
    m = [min(len(a[0]), len(b[0])) for a, b in zip(oc, vc["iii"])]
    rho = spearman(np.concatenate([(a[0] + a[1])[:k] for a, k in zip(oc, m)]), np.concatenate([(b[0] + b[1])[:k] for b, k in zip(vc["iii"], m)]))
    tally = pooled.setdefault("bands", {"x": 0.0, "own": 0.0, "a": [], "b": []})
    tally["x"] += sum(float(reader.codes(v)[0].sum()) for v in versions["iv"][0])
    tally["own"] += sum(float(own150.codes(v)[0].sum()) for v in versions["iv"][0])
    tally["a"].append(np.concatenate([(a[0] + a[1])[:k] for a, k in zip(oc, m)]))
    tally["b"].append(np.concatenate([(b[0] + b[1])[:k] for b, k in zip(vc["iii"], m)]))
    tally.setdefault("same", []).append(float(np.mean(tally["a"][-1] == tally["b"][-1])))
    print("BAND s=%d order=%d places=%d whole a place=%.4f counted=%.4f | iii rank agreement of a place's whole code=%.4f | iv counted by the original's reader over its own=%.4f" % (
        s, reader.order, sum(len(a[0]) for a in oc), sum(float((a[0] + a[1]).sum()) for a in oc) / sum(len(a[0]) for a in oc), sum(float(a[0].sum()) for a in oc) / sum(len(a[0]) for a in oc), rho, x150))
    for code in ("whole", "counted"):
        pick = (lambda a: a[0] + a[1]) if code == "whole" else (lambda a: a[0])
        o = [pick(a) for a in oc]
        v = {k: [pick(a) for a in val] for k, val in vc.items()}
        sections = [("epoch2", locate(o, cut, 2.0)), ("epoch6", locate(o, cut, 6.0))]
        if code == "whole":
            sections.insert(0, ("16bits", 16 * LN2))
        for label, sigma in sections:
            for law_name, law in (("cut", cut), ("odometer", odometer)):
                oo = [law(c, sigma) for c in o]
                mean_epoch = sum(len(c) for c in o) / sum(len(x) for x in oo)
                row = {}
                # i: the law begun START places later on the same codes
                kept = tot = 0
                for c, x in zip(o, oo):
                    y = law(c[START:], sigma) + START
                    past = x[x >= START + 32]
                    kept += int(np.isin(past, y).sum())
                    tot += len(past)
                row["i"] = (kept, tot, 0)
                for k, (_, vstride, off) in versions.items():
                    kept = tot = chance = 0
                    tol = max(float(stride), vstride) / 2
                    for c, x, cv in zip(o, oo, v[k]):
                        ta = (x + 4) * float(stride)
                        y = law(cv, sigma)
                        tb = (y + 4) * vstride + off
                        span = (len(cv) + 4) * vstride
                        far = np.sort((tb - off + FAR * vstride) % span + off)
                        inside = ta[ta <= tb[-1] + tol] if len(tb) else ta[:0]
                        kept += near(inside, tb, tol)
                        chance += near(inside, far, tol)
                        tot += len(inside)
                    row[k] = (kept, tot, chance)
                key = (code, label, law_name)
                acc = pooled.setdefault(key, {k: [0, 0, 0] for k in ("i", "ii", "iii", "iv")} | {"places": 0, "openings": 0})
                acc["places"] += sum(len(c) for c in o)
                acc["openings"] += sum(len(x) for x in oo)
                for k, (a, b, c2) in row.items():
                    acc[k][0] += a
                    acc[k][1] += b
                    acc[k][2] += c2

                def show(t):
                    a, b, c2 = t
                    kp, ch = a / max(b, 1), c2 / max(b, 1)
                    return "kept=%.4f chance=%.4f lift=%.4f" % (kp, ch, (kp - ch) / max(1 - ch, 1e-9))

                print("  s=%d code=%s section=%s (%.3f nats) law=%s mean_epoch=%.3f | i kept=%.4f | ii %s | iii %s | iv %s" % (
                    s, code, label, sigma, law_name, mean_epoch, row["i"][0] / max(row["i"][1], 1), show(row["ii"]), show(row["iii"]), show(row["iv"])))
tally = pooled.pop("bands")
print("POOLED over bands 2 to 6 by places: iii rank agreement of a place's whole code=%.4f, places whose whole code is the same=%s | iv counted by the original's reader over its own=%.4f" % (
    spearman(np.concatenate(tally["a"]), np.concatenate(tally["b"])), " ".join("%.4f" % x for x in tally["same"]), tally["x"] / tally["own"]))
print("POOLED over bands 2 to 6 by openings")
for (code, label, law_name), acc in pooled.items():
    def show(t):
        a, b, c2 = t
        kp, ch = a / max(b, 1), c2 / max(b, 1)
        return "kept=%.4f chance=%.4f lift=%.4f" % (kp, ch, (kp - ch) / max(1 - ch, 1e-9))
    print("  code=%s section=%s law=%s mean_epoch=%.3f | i kept=%.4f | ii %s | iii %s | iv %s" % (
        code, label, law_name, acc["places"] / acc["openings"], acc["i"][0] / max(acc["i"][1], 1), show(acc["ii"]), show(acc["iii"]), show(acc["iv"])))
