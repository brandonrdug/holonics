"""sound_ruler: which places of a speech passage keep their news when its clock changes (G129). A host instrument: a count's
code on public speech, never the machine's face; it enters no law.

The passage is read at its own speed, at double speed and at half speed (the rate renamed, then resampled to 16 kHz), and at
half gain (each sample shifted one bit). Charts:
  half-cycles   October 25's chart (examples/listener/sections.rs): a run of one sign, zeros joined to the run they follow,
                with its length and its peak's octave floor(log2 peak).
  places        the half-cycles whose peak's octave is at the floor or over. A place's words: rho, the half-octave of the
                samples from the place before's start to its own (twice the octave plus the next bit); o, the peak's octave;
                x, whether its sign repeats the place before's. Absolute word (rho, o, x), 10 bits; relative word (rho's
                step, o's step, x).
  samples       the stream at its 16 bits: the best of the four polynomial predictors on the count utterances, the
                residual's bit length and sign counted by the last step's bit length, the rest of the residual flat.
Codes in nats by counts with Witten-Bell backoff (a word given the word before, backed off to the word alone). The cut is
the restarting carry at one section: an opening sets a to its place's code; a place opens where a plus its code passes the
section, and then a is its code.

usage: python3 -I sound_ruler.py RAW_DIR COUNT_UTTERANCES [FLOOR]
RAW_DIR holds orig/NN.raw, fast/NN.raw, slow/NN.raw (signed 16-bit little-endian, 16 kHz). Output: numbers only.
"""
import os
import sys

import numpy as np

raw, n_count = sys.argv[1], int(sys.argv[2])
forced_floor = int(sys.argv[3]) if len(sys.argv) > 3 else None
UNIT = 1_000_000
SECTION = int(round(10 * np.log(2.0) * UNIT))
names = sorted(os.listdir(os.path.join(raw, "orig")))


def load(kind):
    return [np.fromfile(os.path.join(raw, kind, n), dtype="<i2").astype(np.int64) for n in names]


def ilog2(x):
    return np.frexp(np.maximum(x, 1).astype(np.float64))[1] - 1


def half_cycles(v):
    """Starts, lengths, signs and peaks of the runs of one sign, zeros joined to the run they follow."""
    s = np.sign(v)
    idx = np.where(s != 0, np.arange(len(v)), -1)
    last = np.maximum.accumulate(idx)
    filled = np.where(last >= 0, s[np.maximum(last, 0)], 0)
    start = np.flatnonzero(np.concatenate([[True], filled[1:] != filled[:-1]]))
    length = np.diff(np.concatenate([start, [len(v)]]))
    peak = np.maximum.reduceat(np.abs(v), start)
    return start, length, filled[start], peak


def places(v, floor):
    start, length, sign, peak = half_cycles(v)
    keep = (peak >= (1 << floor)) & (sign != 0)
    start, sign, octave = start[keep], sign[keep], ilog2(peak[keep])
    if len(start) == 0:
        e = np.zeros(0, dtype=np.int64)
        return dict(start=e, a=e, r=e, n=0)
    d = np.diff(start)
    lg = ilog2(d)
    rho = np.where(d >= 2, 2 * lg + ((d >> np.maximum(lg - 1, 0)) & 1), 0)
    rho = np.concatenate([[0], np.minimum(rho, 31)])
    x = np.concatenate([[0], (sign[1:] == sign[:-1]).astype(np.int64)])
    a = (rho * 16 + octave) * 2 + x
    drho = np.clip(np.concatenate([[0], np.diff(rho)]), -12, 12) + 12
    do = np.concatenate([[0], np.diff(octave)]) + 15
    r = (drho * 31 + do) * 2 + x
    return dict(start=start, a=a, r=r, n=len(start))


VA, VR = 32 * 16 * 2, 25 * 31 * 2


class Reader:
    """A word given the word before, by counts with Witten-Bell backoff to the word alone."""

    def __init__(self, pieces, key, V, first):
        ctx = np.concatenate([p[key][first - 1:-1] for p in pieces if p["n"] > first])
        k = np.concatenate([p[key][first:] for p in pieces if p["n"] > first])
        self.V = V
        self.c0 = np.bincount(k, minlength=V).astype(np.float64)
        self.full, self.cnt = np.unique(ctx * V + k, return_counts=True)
        self.uctx, at, self.distinct = np.unique(self.full // V, return_index=True, return_counts=True)
        self.tot = np.add.reduceat(self.cnt, at)
        self.key, self.first = key, first

    def codes(self, p):
        """Millionths of a nat a place; places before `first` read zero and are not read places."""
        out = np.zeros(p["n"], dtype=np.int64)
        if p["n"] <= self.first:
            return out
        k, ctx = p[self.key][self.first:], p[self.key][self.first - 1:-1]
        p0 = (self.c0[k] + 0.5) / (self.c0.sum() + 0.5 * self.V)
        q = ctx * self.V + k
        i = np.minimum(np.searchsorted(self.full, q), len(self.full) - 1)
        c = np.where(self.full[i] == q, self.cnt[i], 0).astype(np.float64)
        i = np.minimum(np.searchsorted(self.uctx, ctx), len(self.uctx) - 1)
        seen = self.uctx[i] == ctx
        n, d = np.where(seen, self.tot[i], 0.0), np.where(seen, self.distinct[i], 0.0)
        pr = np.where(seen, (c + d * p0) / np.maximum(n + d, 1e-300), p0)
        out[self.first:] = np.rint(-np.log(pr) * UNIT).astype(np.int64)
        return out


def restarting(code, first, delta=0):
    """Openings among the read places (index `first` and on); the first read place opens."""
    opens = np.zeros(len(code), dtype=bool)
    if len(code) <= first:
        return opens
    opens[first] = True
    a = int(code[first]) + delta
    for t in range(first + 1, len(code)):
        c = int(code[t])
        if a + c > SECTION:
            opens[t] = True
            a = c
        else:
            a += c
    return opens


def image_offset(orig, copy, scale):
    """The resampler's fixed delay: the offset at which most of the original's place starts meet a copy's place start."""
    best_hit, best_c = -1, 0
    for c in range(-12, 13):
        hit = 0
        for po, pc in zip(orig, copy):
            hit += int(np.isin(np.rint(po["start"] * scale).astype(np.int64) + c, pc["start"]).sum())
        if hit > best_hit:
            best_hit, best_c = hit, c
    return best_c


def match(po, pc, scale, offset):
    """For each place of the original, the copy's place that starts within two samples of its start's image, or -1."""
    if pc["n"] == 0:
        return np.full(po["n"], -1, dtype=np.int64)
    img = np.rint(po["start"] * scale).astype(np.int64) + offset
    j = np.clip(np.searchsorted(pc["start"], img), 0, pc["n"] - 1)
    jl = np.maximum(j - 1, 0)
    pick = np.where(np.abs(pc["start"][jl] - img) <= np.abs(pc["start"][j] - img), jl, j)
    return np.where(np.abs(pc["start"][pick] - img) <= 2, pick, -1)


orig, fast, slow = load("orig"), load("fast"), load("slow")
total = sum(len(v) for v in orig)
print("SOUND utterances=%d count=%d read=%d samples=%d seconds=%.1f | fast samples=%d slow samples=%d" % (
    len(orig), n_count, len(orig) - n_count, total, total / 16000, sum(len(v) for v in fast), sum(len(v) for v in slow)))

# (a) half-cycles by the peak's octave.
hist = {}
for kind, vs in (("orig", orig), ("fast", fast), ("slow", slow)):
    h = np.zeros(17, dtype=np.int64)
    for v in vs:
        _, _, sign, peak = half_cycles(v)
        h += np.bincount(np.where(peak > 0, ilog2(peak), 16)[sign != 0], minlength=17)
    hist[kind] = h
print("HALF_CYCLES all=%d a_second=%.0f | fast over orig=%.4f slow over orig=%.4f" % (
    hist["orig"][:16].sum(), hist["orig"][:16].sum() / (total / 16000),
    hist["fast"][:16].sum() / hist["orig"][:16].sum(), hist["slow"][:16].sum() / hist["orig"][:16].sum()))
ratio = {}
for o in range(16):
    if hist["orig"][o]:
        ratio[o] = hist["fast"][o] / hist["orig"][o]
        print("  OCTAVE %2d orig=%8d share=%.4f fast_over_orig=%.4f slow_over_orig=%.4f%s" % (
            o, hist["orig"][o], hist["orig"][o] / hist["orig"][:16].sum(), ratio[o], hist["slow"][o] / hist["orig"][o],
            "" if hist["orig"][o] >= 1000 else " (under 1,000)"))
low = sum(hist["fast"][:6]) / max(sum(hist["orig"][:6]), 1)
high = sum(hist["fast"][12:16]) / max(sum(hist["orig"][12:16]), 1)
big = [o for o in range(16) if hist["orig"][o] >= 1000]
found = [o for o in big if all(ratio[q] >= 0.85 for q in big if q >= o)]
floor = min(found) if found else None
print("A octaves 5 and under fast_over_orig=%.4f | octaves 12 and over=%.4f | floor (least octave from which every octave reads 0.85 or over)=%s" % (
    low, high, floor))
if forced_floor is not None:
    floor = forced_floor
    print("A floor set on the command line for this read: %d" % floor)
if floor is None:
    print("A no floor found by the rule; the rest is not read")
    sys.exit(0)

FIRST = 3
po = [places(v, floor) for v in orig]
pf = [places(v, floor) for v in fast]
ps = [places(v, floor) for v in slow]
pg = [places(v >> 1, max(floor - 1, 0)) for v in orig]
n_places = sum(p["n"] for p in po)
print("PLACES floor=%d places=%d a_second=%.1f of half-cycles=%.4f | fast over orig=%.4f slow over orig=%.4f half gain over orig=%.4f" % (
    floor, n_places, n_places / (total / 16000), n_places / hist["orig"][:16].sum(), sum(p["n"] for p in pf) / n_places,
    sum(p["n"] for p in ps) / n_places, sum(p["n"] for p in pg) / n_places))

ra = Reader(po[:n_count], "a", VA, FIRST)
rr = Reader(po[:n_count], "r", VR, FIRST)


def news(reader, pieces):
    c = [reader.codes(p) for p in pieces]
    return sum(int(x.sum()) for x in c), sum(max(p["n"] - FIRST, 0) for p in pieces), c


read = slice(n_count, len(orig))
out = {}
for tag, pieces in (("orig", po[read]), ("slow", ps[read]), ("fast", pf[read]), ("half gain", pg[read])):
    for name, reader in (("absolute", ra), ("relative", rr)):
        s, n, c = news(reader, pieces)
        out[(tag, name)] = (s, n, c)
        print("  NEWS %-9s %-8s places=%7d nats=%.1f a_place=%.4f" % (tag, name, n, s / UNIT, s / UNIT / max(n, 1)))
for name in ("absolute", "relative"):
    b = out[("orig", name)][0]
    print("B %-8s news over the original's: half speed=%.4f double speed=%.4f half gain=%.4f" % (
        name, out[("slow", name)][0] / b, out[("fast", name)][0] / b, out[("half gain", name)][0] / b))
print("C relative over absolute at the original's speed=%.4f" % (out[("orig", "relative")][0] / out[("orig", "absolute")][0]))

# (d) the restarting cut.
rng = np.random.default_rng(129)
off_s = image_offset(po[read], ps[read], 2.0)
off_f = image_offset(po[read], pf[read], 0.5)
print("D section=%.4f nats | the resampler's delay: half speed %+d samples, double speed %+d samples" % (SECTION / UNIT, off_s, off_f))
for name in ("relative", "absolute"):
    co, cs, cf = out[("orig", name)][2], out[("slow", name)][2], out[("fast", name)][2]
    k = dict(open=0, places=0, over=0, kept_shift=0, cand=0, kept_slow=0, kept_fast=0, m_slow=0, m_fast=0, mplaces=0,
             open_slow=0, places_slow=0, open_fast=0, places_fast=0)
    for q, (p, c) in enumerate(zip(po[read], co)):
        if p["n"] <= FIRST:
            continue
        op = restarting(c, FIRST)
        sh = restarting(c, FIRST, int(rng.integers(0, SECTION)))
        cand = op.copy()
        cand[FIRST] = False
        k["open"] += int(op.sum())
        k["places"] += p["n"] - FIRST
        k["over"] += int((c[FIRST:] > SECTION).sum())
        k["cand"] += int(cand.sum())
        k["kept_shift"] += int((cand & sh).sum())
        for tag, pcs, cc, scale, off in (("slow", ps[read][q], cs[q], 2.0, off_s), ("fast", pf[read][q], cf[q], 0.5, off_f)):
            oc = restarting(cc, FIRST)
            m = match(p, pcs, scale, off)
            ok = m >= FIRST
            k["m_" + tag] += int(ok[FIRST:].sum())
            k["kept_" + tag] += int((cand & ok & oc[np.maximum(m, 0)]).sum())
            k["open_" + tag] += int(oc.sum())
            k["places_" + tag] += max(pcs["n"] - FIRST, 0)
        k["mplaces"] += p["n"] - FIRST
    print("  CUT %-8s mean_epoch=%.3f over_section=%.4f | kept: changed start=%.4f half speed=%.4f double speed=%.4f of %d | "
          "matched: half speed=%.4f double speed=%.4f | a copy's openings a place: half speed=%.4f double speed=%.4f" % (
              name, k["places"] / max(k["open"], 1), k["over"] / max(k["places"], 1), k["kept_shift"] / max(k["cand"], 1),
              k["kept_slow"] / max(k["cand"], 1), k["kept_fast"] / max(k["cand"], 1), k["cand"],
              k["m_slow"] / max(k["mplaces"], 1), k["m_fast"] / max(k["mplaces"], 1),
              k["open_slow"] / max(k["places_slow"], 1), k["open_fast"] / max(k["places_fast"], 1)))


# (e) the sample stream at its 16 bits.
def residuals(v, order):
    e = v.copy()
    for _ in range(order):
        e = np.concatenate([[0], np.diff(e)])
    return e


def bl(x):
    return np.where(x == 0, 0, ilog2(np.abs(x)) + 1)


def stream_news(count, readv):
    best = None
    for order in range(4):
        def parts(vs):
            ctx, key, rest = [], [], []
            for v in vs:
                e = residuals(v, order)[3:]
                step = np.concatenate([[0], np.diff(v)])[2:-1]
                b = bl(e)
                ctx.append(bl(step))
                key.append(b * 2 + (e < 0))
                rest.append(np.maximum(b - 1, 0))
            return np.concatenate(ctx), np.concatenate(key), np.concatenate(rest)
        c_ctx, c_key, c_rest = parts(count)
        tab = np.zeros((18, 44))
        np.add.at(tab, (c_ctx, c_key), 1.0)
        p = (tab + 0.5) / (tab.sum(axis=1, keepdims=True) + 0.5 * 44)

        def total(ctx, key, rest):
            return float(-np.log(p[ctx, key]).sum() + rest.sum() * np.log(2.0))
        t_count = total(c_ctx, c_key, c_rest)
        if best is None or t_count < best[0]:
            r_ctx, r_key, r_rest = parts(readv)
            best = (t_count, order, total(r_ctx, r_key, r_rest), len(r_key))
    return best[1], best[2], best[3]


res = {}
for tag, vs in (("orig", orig), ("fast", fast), ("slow", slow)):
    order, nats, n = stream_news(vs[:n_count], vs[n_count:])
    res[tag] = nats
    print("  STREAM %-4s order=%d samples=%d nats=%.0f a_sample=%.4f bits a_sample=%.4f" % (tag, order, n, nats, nats / n, nats / n / np.log(2.0)))
print("E the sample stream's news over the original's: double speed=%.4f half speed=%.4f" % (res["fast"] / res["orig"], res["slow"] / res["orig"]))
