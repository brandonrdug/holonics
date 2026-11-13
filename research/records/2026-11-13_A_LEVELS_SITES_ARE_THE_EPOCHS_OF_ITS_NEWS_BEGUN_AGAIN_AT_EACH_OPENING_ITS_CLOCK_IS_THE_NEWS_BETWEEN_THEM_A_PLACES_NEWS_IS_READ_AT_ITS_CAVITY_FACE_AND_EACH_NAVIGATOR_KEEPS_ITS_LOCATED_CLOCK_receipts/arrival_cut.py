"""arrival_cut: a ring's own section arrivals as a sound's places, and what of the openings of four laws on their news a change of
start, the shift of rung and a ratio off the ladder keep (G136). A host instrument: a count's code on public speech, never the
machine's face; it enters no law.

The places are ring_arrivals.c's: ring s turns once in 2^s samples free and keeps 1 - 2^-(s + REACH) of its state a sample (its reach
one turn or four, by the directory read); it is read at every sample, and a place is an arrival, a time of the passage (the first
crossing of the section at each whole winding), with |z| there. T is the interval since the arrival before. A place's symbol, two
ways, each (boost, turn) clipped to 3 either way, 49 classes, (0, 0) the ring continuing:
  ring     boost = the step of |z|'s octave on the fixed grid (0 under one unit, else the bit length of its whole part);
           turn = round(4 T / the ring's free turn) - 4: the interval against the ring's own clock, in quarter turns
  passage  boost = round(log2(|z| / |z| at the arrival before)), |z| held at one unit from below;
           turn = round(4 T / the interval before) - 4: the interval against the passage's own last interval, in quarters
The reader counts a place's symbol by the symbol before it (boost and turn clipped to 2 either way: 25 contexts), on the original's
count utterances; a place's code is -ln of its share. What lies under the two widths is released and is not charged.
Rings 3 to 7 of the original; the copies read by the original's reader of the ring named, their times carried to the original's:
  i     the law begun 7 places later on the same codes (openings past the 39th place compared)
  ii    the passage begun 37 samples later, the same ring (the instrument's control: a ring forgets its start)
  ch    the passage begun 37 samples later through the resampler (16 to 48 to 16 kHz), the same ring (the resampler's control)
  ii3   the passage begun 37 and a third samples later (112 samples at 48 kHz), the same ring
  iii   the double-speed copy's ring s-1
  iv    the copy at one and a half times the speed, its ring s-1
Laws on a place's code: cut (band_cut.py's restarting cut: sections the symbol's width ln 49 and those located on the original for a
mean epoch of 2 places and of 6), odometer (at the section for a mean epoch of 6), bright (a place opens where its code alone passes
the symbol's width) and peak (a place opens where its code is above every code within h places before it and not under any within h
places after it: h = 1 and h = 3). An opening is kept where the copy opens within half the ring's free turn, in the original's time;
`whole` is the same within a whole turn. Chance: the copy's openings moved 1,000 of its free turns along, around the utterance.
Lift: (kept - chance) / (1 - chance).
A place itself: `met` where the copy has an arrival within an eighth of the free turn; `same` where the copy's nearest arrival stands
within half a turn and carries the same symbol (over all the original's places; chance by the same move).

usage: python3 -I arrival_cut.py ARRIVALS_DIR RAW_DIR COUNT_UTTERANCES      Output: numbers only.
"""
import os
import sys

import numpy as np
from numpy.lib.stride_tricks import sliding_window_view

arr, raw, n_count = sys.argv[1], sys.argv[2], int(sys.argv[3])
names = sorted(os.listdir(os.path.join(raw, "orig")))
START, FAR, LEAD = 7, 1000, 3
RINGS = range(3, 8)
WIDTH = float(np.log(49.0))
REC = np.dtype([("t", "<f8"), ("m", "<f8"), ("back", "<i4"), ("pad", "<i4")])
# a copy: (directory, the rung read for the original's ring s, its samples in the original's, its start in the original's samples)
COPIES = {"ii": ("shift", 0, 1.0, 37.0), "ch": ("chain", 0, 1.0, 37.0), "ii3": ("third", 0, 1.0, 112.0 / 3.0), "iii": ("fast", -1, 2.0, 0.0), "iv": ("r150", -1, 1.5, 0.0)}
WORDS = ("ring", "passage")


def ring(kind, s):
    return [np.fromfile(os.path.join(arr, kind, "%s.a%d" % (n[:-4], s)), dtype=REC) for n in names]


def symbols(v, turn, word):
    """(context, class, time) a place, for the arrivals LEAD on."""
    t, m = v["t"], v["m"]
    if len(t) < LEAD + 2:
        z = np.zeros(0, dtype=np.int64)
        return z, z, np.zeros(0)
    T = np.diff(t)
    if word == "ring":
        L = np.where(m < 1.0, 0, np.floor(np.log2(np.maximum(m, 1.0))).astype(np.int64) + 1)
        b = np.diff(L)[1:]
        d = np.rint(4.0 * T[1:] / turn) - 4
    else:
        b = np.rint(np.diff(np.log2(np.maximum(m, 1.0))))[1:]
        d = np.rint(4.0 * T[1:] / np.maximum(T[:-1], 1e-9)) - 4
    b = np.clip(b, -3, 3).astype(np.int64)
    d = np.clip(d, -3, 3).astype(np.int64)
    k = (b + 3) * 7 + (d + 3)
    c = (np.clip(b, -2, 2) + 2) * 5 + (np.clip(d, -2, 2) + 2)
    return c[:-1], k[1:], t[LEAD:]


class Reader:
    def __init__(self, seqs, turn, word):
        c, k, _ = (np.concatenate(z) for z in zip(*[symbols(v, turn, word) for v in seqs]))
        tab = np.zeros((25, 49))
        np.add.at(tab, (c, k), 1.0)
        self.p = (tab + 0.5) / (tab.sum(axis=1, keepdims=True) + 0.5 * 49)

    def codes(self, sym):
        return -np.log(self.p[sym[0], sym[1]])


def cut(c, sigma):
    c = c.tolist()
    if not c:
        return np.zeros(0, dtype=np.int64)
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
    if len(c) == 0:
        return np.zeros(0, dtype=np.int64)
    q = np.floor(np.cumsum(c) / sigma).astype(np.int64)
    return np.concatenate([[0], np.nonzero(np.diff(q) > 0)[0] + 1])


def bright(c, sigma):
    if len(c) == 0:
        return np.zeros(0, dtype=np.int64)
    return np.unique(np.concatenate([[0], np.nonzero(c > sigma)[0]]))


def peak(c, h):
    if len(c) == 0:
        return np.zeros(0, dtype=np.int64)
    h = int(h)
    pad = np.concatenate([np.full(h, -np.inf), c, np.full(h, -np.inf)])
    w = sliding_window_view(pad, 2 * h + 1)
    return np.unique(np.concatenate([[0], np.nonzero((c > w[:, :h].max(axis=1)) & (c >= w[:, h + 1:].max(axis=1)))[0]]))


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


def nearest(times_a, times_b):
    """For each of a's times: the distance to b's nearest time and its index (b sorted, not empty)."""
    i = np.clip(np.searchsorted(times_b, times_a), 1, max(len(times_b) - 1, 1))
    if len(times_b) == 1:
        return np.abs(times_a - times_b[0]), np.zeros(len(times_a), dtype=np.int64)
    left, right = np.abs(times_a - times_b[i - 1]), np.abs(times_b[i] - times_a)
    return np.minimum(left, right), np.where(left <= right, i - 1, i)


def near(times_a, times_b, tol):
    if len(times_b) == 0 or len(times_a) == 0:
        return 0
    return int((nearest(times_a, times_b)[0] <= tol).sum())


def moved(t_native, turn_native, scale, off):
    """The copy's times moved FAR of its free turns along, around the utterance, in the original's time; and the order that sorts them."""
    span = t_native[-1] + turn_native if len(t_native) else 1.0
    far = ((t_native + FAR * turn_native) % span) * scale + off
    order = np.argsort(far, kind="stable")
    return far[order], order


def show(t):
    a, b, c2 = t
    kp, ch = a / max(b, 1), c2 / max(b, 1)
    return "kept=%.4f chance=%.4f lift=%.4f" % (kp, ch, (kp - ch) / max(1 - ch, 1e-9))


def lift(t):
    a, b, c2 = t
    kp, ch = a / max(b, 1), c2 / max(b, 1)
    return (kp - ch) / max(1 - ch, 1e-9)


def compare(o, to, v, tv, maps, turn, param, law):
    """Rows by change: (kept, total, chance) within half a free turn and within a whole one."""
    oo = [law(c, param) for c in o]
    kept = tot = 0
    for c, x in zip(o, oo):
        y = law(c[START:], param) + START
        past = x[x >= START + 32]
        kept += int(np.isin(past, y).sum())
        tot += len(past)
    row = {"i": [(kept, tot, 0)] * 2}
    for k, (scale, off, vturn) in maps.items():
        acc = [[0, 0, 0], [0, 0, 0]]
        for x, tc, cv, tcv in zip(oo, to, v[k], tv[k]):
            if len(x) == 0 or len(cv) == 0:
                continue
            y = law(cv, param)
            ta, tb = tc[x], tcv[y] * scale + off
            far, _ = moved(tcv[y], vturn, scale, off)
            for i, tol in enumerate((turn / 2, float(turn))):
                inside = ta[ta <= tb[-1] + tol]
                acc[i][0] += near(inside, tb, tol)
                acc[i][1] += len(inside)
                acc[i][2] += near(inside, far, tol)
        row[k] = [tuple(a) for a in acc]
    return oo, row


def line(tag, param, law_name, o, oo, row):
    me = sum(len(c) for c in o) / max(sum(len(x) for x in oo), 1)
    return "  %s law=%s at %.3f mean_epoch=%.3f | i kept=%.4f | %s" % (tag, law_name, param, me, row["i"][0][0] / max(row["i"][0][1], 1),
        " | ".join("%s %s whole=%.4f" % (k, show(row[k][0]), lift(row[k][1])) for k in COPIES))


def add(key, o, oo, row):
    acc = pooled.setdefault(key, {"places": 0, "openings": 0, "rows": {k: [[0, 0, 0], [0, 0, 0]] for k in ("i",) + tuple(COPIES)}})
    acc["places"] += sum(len(c) for c in o)
    acc["openings"] += sum(len(z) for z in oo)
    for k, pair in row.items():
        for i in range(2):
            for j in range(3):
                acc["rows"][k][i][j] += pair[i][j]


C, R = slice(0, n_count), slice(n_count, len(names))
print("ARRIVALS utterances=%d count=%d read=%d start=%d far_turns=%d symbol_width_nats=%.4f" % (len(names), n_count, len(names) - n_count, START, FAR, WIDTH))
pooled, place = {}, {}
samples = sum(os.path.getsize(os.path.join(raw, "orig", n)) // 2 for n in names[R])
for s in RINGS:
    turn = float(1 << s)
    o_all = ring("orig", s)
    copies = {k: (ring(d, s + ds)[R], float(1 << (s + ds)), scale, off) for k, (d, ds, scale, off) in COPIES.items()}
    n_arr = sum(len(v) for v in o_all[R])
    back = sum(int((v["back"] > 0).sum()) for v in o_all[R]) / max(n_arr, 1)
    print("RING s=%d arrivals=%d a free turn=%.4f with a crossing back before them=%.4f" % (s, n_arr, n_arr * turn / samples, back))
    for word in WORDS:
        reader = Reader(o_all[C], turn, word)
        so = [symbols(v, turn, word) for v in o_all[R]]
        o, to = [reader.codes(z) for z in so], [z[2] for z in so]
        sv = {k: [symbols(u, val[1], word) for u in val[0]] for k, val in copies.items()}
        v = {k: [reader.codes(z) for z in val] for k, val in sv.items()}
        tv = {k: [z[2] for z in val] for k, val in sv.items()}
        maps = {k: (val[2], val[3], val[1]) for k, val in copies.items()}
        x = np.concatenate(o)
        q = np.quantile(x, [0.05, 0.5, 0.95])
        dark = float(np.mean(np.concatenate([z[1] for z in so]) == 24))
        sections = [("width", WIDTH), ("epoch2", locate(o, cut, 2.0)), ("epoch6", locate(o, cut, 6.0))]
        # a place itself under each change
        parts = []
        for k, (scale, off, vturn) in maps.items():
            n = met = same = cmet = csame = 0
            offs = []
            for zo, zv in zip(so, sv[k]):
                if len(zo[2]) == 0 or len(zv[2]) == 0:
                    continue
                tb = zv[2] * scale + off
                inside = zo[2] <= tb[-1] + turn / 2
                ta, ka = zo[2][inside], zo[1][inside]
                dist, j = nearest(ta, tb)
                n += len(ta)
                met += int((dist <= turn / 8).sum())
                same += int(((dist <= turn / 2) & (ka == zv[1][j])).sum())
                offs.append((tb[j] - ta)[dist <= turn / 8])
                far, order = moved(zv[2], vturn, scale, off)
                dist, j = nearest(ta, far)
                cmet += int((dist <= turn / 8).sum())
                csame += int(((dist <= turn / 2) & (ka == zv[1][order][j])).sum())
            offs = np.concatenate(offs) if offs else np.zeros(1)
            acc = place.setdefault((word, k), [0, 0, 0, 0, 0])
            for i, val in enumerate((n, met, same, cmet, csame)):
                acc[i] += val
            parts.append("%s met %s offset median=%.3f spread=%.3f samples; same %s" % (k, show((met, n, cmet)), float(np.median(offs)), float(np.quantile(np.abs(offs - np.median(offs)), 0.5)), show((same, n, csame))))
        print(" WORD %s s=%d places=%d code a place: mean=%.4f quantiles 0.05=%.4f 0.50=%.4f 0.95=%.4f spread=%.4f | the ring continuing (0, 0)=%.4f | places past the section: %s" % (
            word, s, len(x), float(x.mean()), q[0], q[1], q[2], float(x.std() / x.mean()), dark, " ".join("%s(%.3f)=%.4f" % (lab, sg, float((x > sg).mean())) for lab, sg in sections)))
        for part in parts:
            print("  PLACE %s s=%d %s" % (word, s, part))
        laws = [(lab, "cut", cut, sg) for lab, sg in sections] + [("epoch6", "odometer", odometer, sections[2][1]), ("width", "bright", bright, WIDTH), ("h1", "peak", peak, 1.0), ("h3", "peak", peak, 3.0)]
        for label, law_name, law, param in laws:
            oo, row = compare(o, to, v, tv, maps, turn, param, law)
            print(line("%s s=%d %s" % (word, s, label), param, law_name, o, oo, row))
            add((word, label, law_name), o, oo, row)
print("POOLED over rings 3 to 7")
for (word, k), (n, met, same, cmet, csame) in place.items():
    print("  PLACE %s %s places=%d met %s | same %s" % (word, k, n, show((met, n, cmet)), show((same, n, csame))))
for (word, label, law_name), acc in pooled.items():
    r = acc["rows"]
    print("  %s %s law=%s mean_epoch=%.3f | i kept=%.4f | %s" % (word, label, law_name, acc["places"] / max(acc["openings"], 1), r["i"][0][0] / max(r["i"][0][1], 1),
        " | ".join("%s %s whole=%.4f" % (k, show(tuple(r[k][0])), lift(tuple(r[k][1]))) for k in COPIES)))
