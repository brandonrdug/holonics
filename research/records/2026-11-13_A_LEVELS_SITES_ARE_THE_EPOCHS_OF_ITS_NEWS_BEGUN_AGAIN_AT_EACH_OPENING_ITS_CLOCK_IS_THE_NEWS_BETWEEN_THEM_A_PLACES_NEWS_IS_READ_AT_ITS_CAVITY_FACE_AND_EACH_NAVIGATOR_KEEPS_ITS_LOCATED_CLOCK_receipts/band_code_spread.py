"""band_code_spread: how a band's place code is spread, beside band_cut.py's reading (G133; for information, no guess stands on it).
A host instrument: a count's code on public speech, never the machine's face; it enters no law.

The raster, the reader and the two codes are band_cut.py's. A band at a time, over the read utterances:
  the code's quantiles a place (0.05, 0.50, 0.95) and its spread (standard deviation over mean);
  the share of places whose code alone passes the section located for a mean epoch of 6 places, and half of it (band_cut.txt's
  sections, read from its lines): a place brighter than the section opens under every reading;
  the rank agreement of a place's code with the code of the place nearest it in the copy begun 37 samples later.

usage: python3 -I band_code_spread.py RAW_DIR BANDS_DIR COUNT_UTTERANCES BAND_CUT_TXT      Output: numbers only.
"""
import os
import re
import sys

import numpy as np

raw, bands, n_count, cut_txt = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
names = sorted(os.listdir(os.path.join(raw, "orig")))
LN2 = float(np.log(2.0))
SHIFT = 37


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
        c, k, r = parts(v, self.order)
        return -np.log(self.p[c, k]), r * LN2


def band(kind, s):
    return [np.fromfile(os.path.join(bands, kind, "%s.b%d" % (n[:-4], s)), dtype="<i4").astype(np.int64) for n in names]


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


sections = {}
for line in open(cut_txt):
    m = re.match(r"\s+s=(\d) code=(\w+) section=epoch6 \(([0-9.]+) nats\) law=cut", line)
    if m:
        sections[(int(m.group(1)), m.group(2))] = float(m.group(3))
C, R = slice(0, n_count), slice(n_count, len(names))
print("SPREAD utterances=%d count=%d read=%d shift_samples=%d" % (len(names), n_count, len(names) - n_count, SHIFT))
for s in range(2, 7):
    o_all = band("orig", s)
    reader = Reader(o_all[C])
    stride = 1 << s
    oc = [reader.codes(v) for v in o_all[R]]
    sc = [reader.codes(v) for v in band("shift", s)[R]]
    for code in ("whole", "counted"):
        pick = (lambda a: a[0] + a[1]) if code == "whole" else (lambda a: a[0])
        x = np.concatenate([pick(a) for a in oc])
        sigma = sections[(s, code)]
        q = np.quantile(x, [0.05, 0.5, 0.95])
        # the copy's place q stands at the original's time (q + 4) 2^s + 37; the original's place nearest it is q + round(37 / 2^s)
        k = int(np.floor(SHIFT / stride + 0.5))
        a, b = [], []
        for u, v in zip(oc, sc):
            pu, pv = pick(u), pick(v)
            n = min(len(pu) - k, len(pv))
            a.append(pu[k:k + n])
            b.append(pv[:n])
        print("  s=%d code=%s places=%d mean=%.4f quantiles 0.05=%.4f 0.50=%.4f 0.95=%.4f spread=%.4f | section for a mean epoch of 6=%.3f: places past it=%.6f past half of it=%.6f | rank agreement with the place nearest it in the shifted copy (%d samples off)=%.4f" % (
            s, code, len(x), float(x.mean()), q[0], q[1], q[2], float(x.std() / x.mean()), sigma, float((x > sigma).mean()), float((x > sigma / 2).mean()),
            abs(k * stride - SHIFT), spearman(np.concatenate(a), np.concatenate(b))))
