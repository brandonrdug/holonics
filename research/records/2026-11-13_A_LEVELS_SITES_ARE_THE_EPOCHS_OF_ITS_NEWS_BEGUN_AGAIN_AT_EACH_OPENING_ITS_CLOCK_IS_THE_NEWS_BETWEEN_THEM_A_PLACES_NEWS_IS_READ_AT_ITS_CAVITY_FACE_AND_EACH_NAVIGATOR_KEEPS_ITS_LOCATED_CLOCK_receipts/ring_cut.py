"""ring_cut: the restarting cut on the places of a ladder of driven rings read once a turn, and what of its openings a change of start,
the shift of rung and a ratio off the ladder keep (G135). A host instrument: a count's code on public speech, never the machine's
face; it enters no law.

The raster is ring_sections.c's: ring s turns once in 2^s samples and keeps 1 - 2^-(s + REACH) of its state a sample (its reach one
turn or four, by the directory read); a place is one turn; at a place the ring's octave L and its lift (the dynamic section's, in
quarter turns). A place's symbol is its ratio to the place before it
at the two declared widths: the boost dL = L - L_before clipped to 3 either way (octaves) and the turn d = the lift's advance less the
free ring's 4, clipped to 3 either way (quarter turns): 49 classes, of which (0, 0) is the ring continuing. The reader counts a
place's symbol by the place before it (its boost and turn clipped to 2 either way: 25 contexts), on the original's count utterances;
a place's code is -ln of its share. What lies under the two widths is released and is not charged.
Rings 3 to 7 of the original; the copies as band_cut.py's four changes, read by the original's reader of the ring named:
  i    the cut begun 7 places later on the same codes (openings past the 39th place compared)
  ii   the passage begun 37 samples later, the same ring
  iii  the double-speed copy's ring s-1
  iv   the copy at one and a half times the speed, its ring s-1
The cut, the odometer, chance and lift are band_cut.py's. Sections: the symbol's own width (ln 49) and those located on the original for
a mean epoch of 2 places and of 6. Two laws with no sum, beside them: bright (a place opens where its code alone passes the symbol's
width) and events (a place opens where its symbol is not the ring continuing). An opening is kept where the copy opens within half the wider of the two strides in the original's
time (band_cut.py's); beside it the same with a whole stride (the two places overlap). Loud: the original's opening stands at a place
whose octave is within 3 of the utterance's 0.95 quantile for that ring.
The column: the places of ring 3 (ring 2 of a faster copy); a column's news is the sum over the rings of the code of the ring's place
that holds it, divided evenly over the columns that place holds; the cut on the columns, sections located for a mean epoch of 2
columns and of 6.

usage: python3 -I ring_cut.py RAW_DIR RINGS_DIR COUNT_UTTERANCES      Output: numbers only.
"""
import os
import sys

import numpy as np

raw, rings, n_count = sys.argv[1], sys.argv[2], int(sys.argv[3])
names = sorted(os.listdir(os.path.join(raw, "orig")))
START, SHIFT, FAR, LEAD = 7, 37, 1000, 2
RINGS = range(3, 8)
WIDTH = float(np.log(49.0))


def ring(kind, s):
    out = []
    for n in names:
        r = np.fromfile(os.path.join(rings, kind, "%s.r%d" % (n[:-4], s)), dtype="<i4").astype(np.int64).reshape(-1, 2)
        out.append((r[:, 0], r[:, 1]))
    return out


def symbols(v):
    """(context, class, octave) a place, for the places LEAD on."""
    L, lift = v
    b = np.clip(np.diff(L), -3, 3)
    d = np.clip(np.diff(lift) - 4, -3, 3)
    k = (b + 3) * 7 + (d + 3)
    c = (np.clip(b, -2, 2) + 2) * 5 + (np.clip(d, -2, 2) + 2)
    return c[:-1], k[1:], L[LEAD:]


class Reader:
    def __init__(self, seqs):
        c, k, _ = (np.concatenate(z) for z in zip(*[symbols(v) for v in seqs if len(v[0]) > 8]))
        tab = np.zeros((25, 49))
        np.add.at(tab, (c, k), 1.0)
        self.p = (tab + 0.5) / (tab.sum(axis=1, keepdims=True) + 0.5 * 49)

    def codes(self, v):
        c, k, _ = symbols(v)
        return -np.log(self.p[c, k])


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


def bright(c, sigma):
    return np.unique(np.concatenate([[0], np.nonzero(c > sigma)[0]]))


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


def show(t):
    a, b, c2 = t
    kp, ch = a / max(b, 1), c2 / max(b, 1)
    return "kept=%.4f chance=%.4f lift=%.4f" % (kp, ch, (kp - ch) / max(1 - ch, 1e-9))


def compare(o, v, versions, stride, sigma, law, lead, loud=None):
    """Rows by change: (kept, total, chance) at half a stride, at a whole stride, and at half a stride on the loud openings."""
    oo = [law(c, sigma) for c in o]
    row = {}
    kept = tot = 0
    for c, x in zip(o, oo):
        y = law(c[START:], sigma) + START
        past = x[x >= START + 32]
        kept += int(np.isin(past, y).sum())
        tot += len(past)
    row["i"] = [(kept, tot, 0)] * 3
    for k, (vstride, off) in versions.items():
        acc = [[0, 0, 0] for _ in range(3)]
        for j, (c, x, cv) in enumerate(zip(o, oo, v[k])):
            ta = (x + lead) * float(stride)
            tb = (law(cv, sigma) + lead) * vstride + off
            span = (len(cv) + lead) * vstride
            far = np.sort((tb - off + FAR * vstride) % span + off)
            for i, tol in enumerate((max(float(stride), vstride) / 2, max(float(stride), vstride), max(float(stride), vstride) / 2)):
                keep = ta <= tb[-1] + tol if len(tb) else np.zeros(len(ta), dtype=bool)
                if i == 2:
                    if loud is None:
                        continue
                    keep = keep & loud[j][x]
                inside = ta[keep]
                acc[i][0] += near(inside, tb, tol)
                acc[i][1] += len(inside)
                acc[i][2] += near(inside, far, tol)
        row[k] = [tuple(a) for a in acc]
    return oo, row


def line(tag, sigma, law_name, o, oo, row):
    me = sum(len(c) for c in o) / sum(len(x) for x in oo)
    return "  %s section=%.3f nats law=%s mean_epoch=%.3f | i kept=%.4f | ii %s; overlap %s; loud %s | iii %s; overlap %s; loud %s | iv %s; overlap %s; loud %s" % (
        tag, sigma, law_name, me, row["i"][0][0] / max(row["i"][0][1], 1),
        show(row["ii"][0]), show(row["ii"][1]), show(row["ii"][2]), show(row["iii"][0]), show(row["iii"][1]), show(row["iii"][2]),
        show(row["iv"][0]), show(row["iv"][1]), show(row["iv"][2]))


def add(key, o, oo, row):
    acc = pooled.setdefault(key, {"places": 0, "openings": 0, "rows": {k: [[0, 0, 0] for _ in range(3)] for k in ("i", "ii", "iii", "iv")}})
    acc["places"] += sum(len(c) for c in o)
    acc["openings"] += sum(len(z) for z in oo)
    for k, trip in row.items():
        for i in range(3):
            for j in range(3):
                acc["rows"][k][i][j] += trip[i][j]


C, R = slice(0, n_count), slice(n_count, len(names))
print("RINGS utterances=%d count=%d read=%d start=%d shift_samples=%d far_strides=%d symbol_width_nats=%.4f" % (len(names), n_count, len(names) - n_count, START, SHIFT, FAR, WIDTH))
pooled, cols = {}, {"o": None, "ii": None, "iii": None, "iv": None}
for s in RINGS:
    o_all = ring("orig", s)
    reader = Reader(o_all[C])
    stride = 1 << s
    vers = {"ii": (ring("shift", s)[R], float(stride), float(SHIFT)), "iii": (ring("fast", s - 1)[R], 2.0 * (stride >> 1), 0.0), "iv": (ring("r150", s - 1)[R], 1.5 * (stride >> 1), 0.0)}
    o = [reader.codes(v) for v in o_all[R]]
    v = {k: [reader.codes(u) for u in val[0]] for k, val in vers.items()}
    versions = {k: (val[1], val[2]) for k, val in vers.items()}
    syms = [symbols(u) for u in o_all[R]]
    loud = [u[2] >= np.quantile(u[2], 0.95) - 3 for u in syms]
    x = np.concatenate(o)
    q = np.quantile(x, [0.05, 0.5, 0.95])
    dark = float(np.mean(np.concatenate([u[1] for u in syms]) == 24))
    own150 = Reader(ring("r150", s - 1)[C])
    x150 = sum(float(reader.codes(u).sum()) for u in vers["iv"][0]) / sum(float(own150.codes(u).sum()) for u in vers["iv"][0])
    # agreement of a place's symbol and code with the place it meets: iii one to one; ii the original's place nearest the copy's
    m3 = [min(len(a), len(b)) for a, b in zip(o, v["iii"])]
    same3 = float(np.mean(np.concatenate([a[1][:k] for a, k in zip(syms, m3)]) == np.concatenate([symbols(u)[1][:k] for u, k in zip(vers["iii"][0], m3)])))
    rho3 = spearman(np.concatenate([a[:k] for a, k in zip(o, m3)]), np.concatenate([b[:k] for b, k in zip(v["iii"], m3)]))
    k2 = int(np.floor(SHIFT / stride + 0.5))
    m2 = [min(len(a) - k2, len(b)) for a, b in zip(o, v["ii"])]
    same2 = float(np.mean(np.concatenate([a[1][k2:k2 + k] for a, k in zip(syms, m2)]) == np.concatenate([symbols(u)[1][:k] for u, k in zip(vers["ii"][0], m2)])))
    rho2 = spearman(np.concatenate([a[k2:k2 + k] for a, k in zip(o, m2)]), np.concatenate([b[:k] for b, k in zip(v["ii"], m2)]))
    sections = [("width", WIDTH), ("epoch2", locate(o, cut, 2.0)), ("epoch6", locate(o, cut, 6.0))]
    print("RING s=%d places=%d code a place: mean=%.4f quantiles 0.05=%.4f 0.50=%.4f 0.95=%.4f spread=%.4f | the ring continuing (0, 0)=%.4f of places | loud places=%.4f | places past the section: %s | ii: symbol the same=%.4f rank agreement of the code=%.4f (%d samples off) | iii: symbol the same=%.4f rank agreement=%.4f | iv counted by the original's reader over its own=%.4f" % (
        s, len(x), float(x.mean()), q[0], q[1], q[2], float(x.std() / x.mean()), dark, float(np.mean(np.concatenate(loud))),
        " ".join("%s(%.3f)=%.4f" % (lab, sg, float((x > sg).mean())) for lab, sg in sections), same2, rho2, abs(k2 * stride - SHIFT), same3, rho3, x150))
    for label, sigma in sections:
        for law_name, law in (("cut", cut), ("odometer", odometer)):
            oo, row = compare(o, v, versions, stride, sigma, law, LEAD, loud)
            print(line("s=%d %s" % (s, label), sigma, law_name, o, oo, row))
            add((label, law_name), o, oo, row)
    oo, row = compare(o, v, versions, stride, WIDTH, bright, LEAD, loud)
    print(line("s=%d width" % s, WIDTH, "bright", o, oo, row))
    add(("width", "bright"), o, oo, row)
    ev_o = [(u[1] != 24).astype(np.float64) for u in syms]
    ev_v = {k: [(symbols(u)[1] != 24).astype(np.float64) for u in val[0]] for k, val in vers.items()}
    oo, row = compare(ev_o, ev_v, versions, stride, 0.5, bright, LEAD, loud)
    print(line("s=%d symbol" % s, 0.5, "events", ev_o, oo, row))
    add(("symbol", "events"), ev_o, oo, row)
    # the column: every ring's place code laid evenly over the places of the finest ring (ring 3; ring 2 of a faster copy) it holds
    for key, seqs in (("o", o), ("ii", v["ii"]), ("iii", v["iii"]), ("iv", v["iv"])):
        if cols[key] is None:
            cols[key] = [np.zeros(len(c) + LEAD) for c in seqs]
        w = 1 << (s - 3)
        for col, c in zip(cols[key], seqs):
            spread = np.repeat(c / w, w)
            a = LEAD * w
            n = min(len(spread), len(col) - a)
            col[a:a + n] += spread[:n]
print("POOLED over rings 3 to 7 by openings")
for (label, law_name), acc in pooled.items():
    r = {k: [tuple(t) for t in trip] for k, trip in acc["rows"].items()}
    print("  section=%s law=%s mean_epoch=%.3f | i kept=%.4f | ii %s; overlap %s; loud %s | iii %s; overlap %s; loud %s | iv %s; overlap %s; loud %s" % (
        label, law_name, acc["places"] / acc["openings"], r["i"][0][0] / max(r["i"][0][1], 1),
        show(r["ii"][0]), show(r["ii"][1]), show(r["ii"][2]), show(r["iii"][0]), show(r["iii"][1]), show(r["iii"][2]), show(r["iv"][0]), show(r["iv"][1]), show(r["iv"][2])))
oc = cols["o"]
x = np.concatenate(oc)
versions = {"ii": (8.0, float(SHIFT)), "iii": (8.0, 0.0), "iv": (6.0, 0.0)}
vc = {k: cols[k] for k in versions}
sections = [("epoch2", locate(oc, cut, 2.0)), ("epoch6", locate(oc, cut, 6.0))]
print("COLUMN columns=%d news a column: mean=%.4f quantiles 0.05=%.4f 0.50=%.4f 0.95=%.4f spread=%.4f | columns past the section: %s" % (
    len(x), float(x.mean()), *np.quantile(x, [0.05, 0.5, 0.95]), float(x.std() / x.mean()), " ".join("%s(%.3f)=%.4f" % (lab, sg, float((x > sg).mean())) for lab, sg in sections)))
for label, sigma in sections:
    for law_name, law in (("cut", cut), ("odometer", odometer)):
        oo, row = compare(oc, vc, versions, 8, sigma, law, 0)
        print(line("column %s" % label, sigma, law_name, oc, oo, row))
