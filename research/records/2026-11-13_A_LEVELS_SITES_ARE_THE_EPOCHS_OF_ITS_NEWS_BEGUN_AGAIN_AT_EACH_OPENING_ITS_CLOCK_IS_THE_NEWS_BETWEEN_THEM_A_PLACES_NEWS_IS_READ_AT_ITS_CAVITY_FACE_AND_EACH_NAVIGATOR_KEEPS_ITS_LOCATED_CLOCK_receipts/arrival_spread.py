"""arrival_spread: where a place's symbol changes under a change (for information beside G136's score; read after it). A host instrument.

arrival_cut.py's places, symbols and nearest arrivals. A place is loud where |z| stands within 3 octaves of the 0.95 quantile of |z|
over its utterance's arrivals on that ring. By ring and pooled, for the copies ch, ii3, iii: the share of places loud; the symbol the
same on the loud places and on the rest; and, over the places whose nearest arrival of the copy stands within half a free turn, the
share whose boost differs and the share whose turn differs.

usage: python3 -I arrival_spread.py ARRIVALS_DIR RAW_DIR COUNT_UTTERANCES      Output: numbers only.
"""
import os
import sys

import numpy as np

arr, raw, n_count = sys.argv[1], sys.argv[2], int(sys.argv[3])
names = sorted(os.listdir(os.path.join(raw, "orig")))
LEAD = 3
REC = np.dtype([("t", "<f8"), ("m", "<f8"), ("back", "<i4"), ("pad", "<i4")])
COPIES = {"ch": ("chain", 0, 1.0, 37.0), "ii3": ("third", 0, 1.0, 112.0 / 3.0), "iii": ("fast", -1, 2.0, 0.0)}


def ring(kind, s):
    return [np.fromfile(os.path.join(arr, kind, "%s.a%d" % (n[:-4], s)), dtype=REC) for n in names[n_count:]]


def digits(v, turn, word):
    t, m = v["t"], v["m"]
    T = np.diff(t)
    if word == "ring":
        L = np.where(m < 1.0, 0, np.floor(np.log2(np.maximum(m, 1.0))).astype(np.int64) + 1)
        b, d = np.diff(L)[1:], np.rint(4.0 * T[1:] / turn) - 4
    else:
        b, d = np.rint(np.diff(np.log2(np.maximum(m, 1.0))))[1:], np.rint(4.0 * T[1:] / np.maximum(T[:-1], 1e-9)) - 4
    return np.clip(b, -3, 3).astype(np.int64)[1:], np.clip(d, -3, 3).astype(np.int64)[1:], t[LEAD:], m[LEAD:]


def nearest(ta, tb):
    i = np.clip(np.searchsorted(tb, ta), 1, len(tb) - 1)
    left, right = np.abs(ta - tb[i - 1]), np.abs(tb[i] - ta)
    return np.minimum(left, right), np.where(left <= right, i - 1, i)


tot = {}
for s in range(3, 8):
    turn = float(1 << s)
    o_all = ring("orig", s)
    for word in ("ring", "passage"):
        for k, (d, ds, scale, off) in COPIES.items():
            c_all = ring(d, s + ds)
            acc = np.zeros(8)
            for vo, vc in zip(o_all, c_all):
                if len(vo) < LEAD + 3 or len(vc) < LEAD + 3:
                    continue
                bo, do, to, mo = digits(vo, turn, word)
                bc, dc, tc, _ = digits(vc, float(1 << (s + ds)), word)
                tb = tc * scale + off
                inside = to <= tb[-1] + turn / 2
                bo, do, to, mo = bo[inside], do[inside], to[inside], mo[inside]
                dist, j = nearest(to, tb)
                hit = dist <= turn / 2
                same = hit & (bo == bc[j]) & (do == dc[j])
                loud = np.log2(np.maximum(mo, 1.0)) >= np.log2(max(float(np.quantile(vo["m"], 0.95)), 1.0)) - 3
                acc += [len(to), loud.sum(), same[loud].sum(), same[~loud].sum(), hit.sum(), (hit & (bo != bc[j])).sum(), (hit & (do != dc[j])).sum(), (~loud).sum()]
            tot[(word, k)] = tot.get((word, k), np.zeros(8)) + acc
            n, nl, sl, sq, h, db, dd, nq = acc
            print("s=%d %s %s places=%d loud=%.4f | the same: loud=%.4f the rest=%.4f | of the places met within half a turn: boost differs=%.4f turn differs=%.4f" % (
                s, word, k, n, nl / n, sl / max(nl, 1), sq / max(nq, 1), db / max(h, 1), dd / max(h, 1)))
for (word, k), (n, nl, sl, sq, h, db, dd, nq) in tot.items():
    print("POOLED %s %s places=%d loud=%.4f | the same: loud=%.4f the rest=%.4f | of the places met within half a turn: boost differs=%.4f turn differs=%.4f" % (
        word, k, n, nl / n, sl / max(nl, 1), sq / max(nq, 1), db / max(h, 1), dd / max(h, 1)))
