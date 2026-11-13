"""site_ruler: the law of sites read on any symbol stream by one program (G137). A host instrument: a count's code on public
material, never the machine's face; it enters no law.

A stream is a list of regions; a region is its symbols (whole numbers under the alphabet's width A) and a coordinate a place (an
index, or a time). A boundary supplies those and nothing else; everything below the three boundaries at the foot of this file is one
path for every stream.

The reader: counts with Witten-Bell backoff, two symbols back, on the stream's count regions; a region is begun fresh (two break
marks before it). A place's news is -ln of its share, in nats.

Laws on a region's news c, S its running sum, sigma the section (a place u is GREATER than t where c_u > c_t, or equal and
earlier; u REACHES t where |S_u - S_t| < sigma):
  O  odometer      a place opens where floor(S / sigma) rises; a region's first place opens
  C  carried cut   a place opens when the news since the last opening, its own included, passes sigma; the first place opens
  A  the claim in the order of arrival (the earlier first): a place is a site unless a site reaches it, so a place opens when
                   the news from the last site's arrival to its own is sigma or more; the first place opens. It is the carried
                   cut with a stride measured from arrival to arrival; its first round is the places of sigma or more
  G  the claim     in the order of news (the most first): a place is a site unless a site reaches it (its rounds: round one, then the first round of
                   what the sites of round one do not reach, and on)
  P  first round   a place is a site where no greater place reaches it: its isolation (the news to the last place before it that
                   is no less, and to the first place after it that is more, the lesser of the two) is sigma or more
  W  a window      G136's law on a count of places, for information: above every place within 3 before, not under any within 3 after
Extents: `width`, sigma = ln A; `epoch2` and `epoch6`, sigma located on the stream's read regions for a mean epoch of 2 places and
of 6, each law its own.

Changes, the copy read by the same reader and cut at the same sigma:
  start      the region begun 7 places later
  insert q   after a place, at q of places, the reader's most expected symbol there is inserted
  flip q     at q of places the symbol is replaced by another, drawn from the reader's face there
  and the changes a boundary supplies of its own (a copy of the regions with its coordinates carried to the original's)
A site is kept where the copy has a site within the change's tolerance of its coordinate; sites past the 39th place of a region
are compared. The three made changes are changes of places, so on every stream they are compared by place (a place's index its
coordinate, the same place kept); a boundary's own change is compared on the boundary's coordinate. Chance: the copy's sites
moved FAR along, around the region (FAR places for a made change, FAR steps of the boundary's coordinate for its own).
Lift: (kept - chance) / (1 - chance). `same`: the share of the original's places whose symbol stands in the copy at their
coordinate; `untouched`: the share whose news is the same there.

usage: python3 -I site_ruler.py made                                                       (the instrument's dry run and checks)
       python3 -I site_ruler.py octets COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES
       python3 -I site_ruler.py arrivals ARRIVALS_DIR RAW_DIR COUNT_UTTERANCES
Output: numbers only.
"""
import os
import sys

import numpy as np
from numpy.lib.stride_tricks import sliding_window_view

START, MARGIN, FAR, SEED, SHORT = 7, 32, 1000, 137, 64
RATES = (0.05, 0.25)
INF = float("inf")


# ---------------------------------------------------------------------------------------------------------------- the reader
def table(ctx, key, V):
    full, cnt = np.unique(ctx * V + key, return_counts=True)
    uctx, at, distinct = np.unique(full // V, return_index=True, return_counts=True)
    return full, cnt, uctx, np.add.reduceat(cnt, at), distinct


def backoff(tab, ctx, key, lower, V):
    full, cnt, uctx, tot, distinct = tab
    k = ctx * V + key
    i = np.minimum(np.searchsorted(full, k), len(full) - 1)
    c = np.where(full[i] == k, cnt[i], 0).astype(np.float64)
    i = np.minimum(np.searchsorted(uctx, ctx), len(uctx) - 1)
    seen = uctx[i] == ctx
    n, d = np.where(seen, tot[i], 0).astype(np.float64), np.where(seen, distinct[i], 0).astype(np.float64)
    return np.where(seen, (c + d * lower) / np.maximum(n + d, 1e-300), lower)


def row(tab, ctx, lower, V):
    """The face over the whole alphabet at one context."""
    full, cnt, uctx, tot, distinct = tab
    i = int(np.searchsorted(uctx, ctx))
    if i == len(uctx) or uctx[i] != ctx:
        return lower
    a, b = np.searchsorted(full, ctx * V), np.searchsorted(full, (ctx + 1) * V)
    c = np.zeros(V)
    c[full[a:b] - ctx * V] = cnt[a:b]
    return (c + distinct[i] * lower) / (tot[i] + distinct[i])


def joined(regions, A):
    mark = np.array([A, A], dtype=np.int64)
    out = []
    for r in regions:
        out.append(mark)
        out.append(r)
    return np.concatenate(out) if out else np.zeros(0, dtype=np.int64)


class Reader:
    def __init__(self, regions, A):
        self.A, self.V = A, A + 1
        train = joined(regions, A)
        self.c0 = np.bincount(train, minlength=self.V).astype(np.float64)
        self.p0 = (self.c0 + 0.5) / (self.c0.sum() + 0.5 * self.V)
        self.t1 = table(train[:-1], train[1:], self.V)
        self.t2 = table(train[1:-1] * self.V + train[:-2], train[2:], self.V)

    def codes(self, regions):
        """A place's news, a region at a time."""
        seq = joined(regions, self.A)
        if len(seq) == 0:
            return []
        key, b1, b2 = seq[2:], seq[1:-1], seq[:-2]
        p1 = backoff(self.t1, b1, key, self.p0[key], self.V)
        p2 = backoff(self.t2, b1 * self.V + b2, key, p1, self.V)
        c = np.concatenate([[0.0, 0.0], -np.log(p2)])
        out, at = [], 0
        for r in regions:
            out.append(c[at + 2: at + 2 + len(r)])
            at += 2 + len(r)
        return out

    def faces(self, b1, b2):
        """For each (the symbol before, the one before that): the index of its face in a list of faces over the alphabet, the
        break mark left out."""
        key = b1 * self.V + b2
        ukey, inv = np.unique(key, return_inverse=True)
        rows, one = [], {}
        for k in ukey.tolist():
            a = k // self.V
            if a not in one:
                one[a] = row(self.t1, a, self.p0, self.V)
            f = row(self.t2, k, one[a], self.V).copy()
            f[self.A] = 0.0
            rows.append(f / f.sum())
        return rows, inv


# --------------------------------------------------------------------------------------------------------------- the changes
def begun_later(reader, sym, x, q, rng):
    return sym[START:], x[START:]


def insert_after(sym, x, pick, new):
    """`new[i]` inserted after the i-th picked place; an inserted place has no coordinate."""
    n = len(sym)
    at = np.arange(n) + np.concatenate([[0], np.cumsum(pick)[:-1]])
    out = np.empty(n + int(pick.sum()), dtype=np.int64)
    xo = np.full(len(out), np.nan)
    out[at], xo[at] = sym, x
    out[at[pick] + 1] = new
    return out, xo


def inserted(reader, sym, x, q, rng):
    pick = rng.random(len(sym)) < q
    pick[:1] = False
    if not pick.any():
        return sym, x
    t = np.flatnonzero(pick)
    rows, inv = reader.faces(sym[t], sym[t - 1])
    top = np.array([int(np.argmax(f)) for f in rows], dtype=np.int64)
    return insert_after(sym, x, pick, top[inv])


def flipped(reader, sym, x, q, rng):
    pick = rng.random(len(sym)) < q
    pick[:2] = False
    if not pick.any():
        return sym, x
    t = np.flatnonzero(pick)
    rows, inv = reader.faces(sym[t - 1], sym[t - 2])
    out = sym.copy()
    for g in range(len(rows)):
        at = t[inv == g]
        f = rows[g]
        for own in np.unique(sym[at]).tolist():
            h = f.copy()
            h[own] = 0.0
            if h.sum() <= 0.0:
                h = np.ones(len(f))
                h[own] = h[reader.A] = 0.0
            who = at[sym[at] == own]
            out[who] = rng.choice(len(f), size=len(who), p=h / h.sum())
    return out, x


# ------------------------------------------------------------------------------------------------------------------ the laws
def odometer(c, sigma):
    q = np.floor(np.cumsum(c) / sigma).astype(np.int64)
    return np.concatenate([[0], np.flatnonzero(np.diff(q) > 0) + 1])


def cut(c, sigma):
    c = c.tolist()
    out, a = [0], c[0]
    for t in range(1, len(c)):
        v = c[t]
        if a + v > sigma:
            out.append(t)
            a = v
        else:
            a += v
    return np.asarray(out, dtype=np.int64)


def arrival(c, sigma):
    S = np.cumsum(c).tolist()
    out, last = [0], S[0]
    for t in range(1, len(S)):
        if S[t] - last >= sigma:
            out.append(t)
            last = S[t]
    return np.asarray(out, dtype=np.int64)


def isolation(c, S):
    """The lesser of S_t - S_u at the last u < t with c_u >= c_t and S_u - S_t at the first u > t with c_u > c_t."""
    n = len(c)
    before, after = np.full(n, -1, dtype=np.int64), np.full(n, -1, dtype=np.int64)
    cl, stack = c.tolist(), []
    for t in range(n):
        v = cl[t]
        while stack and cl[stack[-1]] < v:
            after[stack.pop()] = t
        if stack:
            before[t] = stack[-1]
        stack.append(t)
    back = np.where(before >= 0, S - S[np.maximum(before, 0)], INF)
    fore = np.where(after >= 0, S[np.maximum(after, 0)] - S, INF)
    return np.minimum(back, fore)


def claim(c, sigma):
    """The sites of the claim and the round each entered in."""
    S = np.cumsum(c)
    alive = np.arange(len(c))
    sites, rounds, r = [], [], 0
    while len(alive):
        r += 1
        Sa = S[alive]
        new = alive[isolation(c[alive], Sa) >= sigma]
        sites.append(new)
        rounds.append(np.full(len(new), r, dtype=np.int64))
        Sn = S[new]
        i = np.searchsorted(Sn, Sa)
        left = np.where(i > 0, Sa - Sn[np.maximum(i - 1, 0)], INF)
        right = np.where(i < len(Sn), Sn[np.minimum(i, len(Sn) - 1)] - Sa, INF)
        alive = alive[np.minimum(left, right) >= sigma]
    sites, rounds = np.concatenate(sites), np.concatenate(rounds)
    order = np.argsort(sites)
    return sites[order], rounds[order]


def window(c, h=3):
    pad = np.concatenate([np.full(h, -INF), c, np.full(h, -INF)])
    w = sliding_window_view(pad, 2 * h + 1)
    return np.flatnonzero((c > w[:, :h].max(axis=1)) & (c >= w[:, h + 1:].max(axis=1)))


LAWS = ("O", "C", "A", "G", "P", "W")


def sites_of(law, c, rho, sigma):
    if law == "O":
        return odometer(c, sigma)
    if law == "C":
        return cut(c, sigma)
    if law == "A":
        return arrival(c, sigma)
    if law == "G":
        return claim(c, sigma)[0]
    if law == "P":
        return np.flatnonzero(rho >= sigma)
    return window(c)


def locate(law, codes, rhos, target, top):
    places = sum(len(c) for c in codes)
    if law == "P":
        rho = np.sort(np.concatenate(rhos))[::-1]
        return float(rho[max(int(round(places / target)) - 1, 0)])
    lo, hi = 0.0, top
    for _ in range(22):
        mid = (lo + hi) / 2
        if places / sum(len(sites_of(law, c, r, mid)) for c, r in zip(codes, rhos)) < target:
            lo = mid
        else:
            hi = mid
    return hi


# -------------------------------------------------------------------------------------------------------------- the comparison
def nearest(a, b):
    """For each of a's coordinates: the distance to b's nearest and its index (b sorted, not empty)."""
    if len(b) == 1:
        return np.abs(a - b[0]), np.zeros(len(a), dtype=np.int64)
    i = np.clip(np.searchsorted(b, a), 1, len(b) - 1)
    left, right = np.abs(a - b[i - 1]), np.abs(b[i] - a)
    return np.minimum(left, right), np.where(left <= right, i - 1, i)


def compare(xo, so, xc, sc, tol, far, step):
    """(which of the original's compared sites are kept, how many stand at the moved copy) for one region."""
    live = np.isfinite(xc)
    if len(so) == 0 or not live.any():
        return np.zeros(0, dtype=bool), np.zeros(0, dtype=np.int64), 0
    lo, hi = float(xc[live].min()), float(xc[live].max())
    so = so[so >= START + MARGIN]
    ta = xo[so]
    inside = (ta >= lo - tol) & (ta <= hi + tol)
    so, ta = so[inside], ta[inside]
    tb = xc[sc]
    tb = np.sort(tb[np.isfinite(tb)])
    if len(ta) == 0 or len(tb) == 0:
        return np.zeros(len(ta), dtype=bool), so, 0
    kept = nearest(ta, tb)[0] <= tol
    moved = np.sort((tb - lo + far) % (hi - lo + step) + lo)
    return kept, so, int((nearest(ta, moved)[0] <= tol).sum())


def lift(k, n, ch):
    kp, cp = k / max(n, 1), ch / max(n, 1)
    return kp, cp, (kp - cp) / max(1 - cp, 1e-9)


def show(t):
    return "kept=%.4f chance=%.4f lift=%.4f" % lift(*t)


def read(kind, streams):
    pooled, by_round, extents = {}, {}, ("width", "epoch2", "epoch6")
    for si, st in enumerate(streams):
        A, name = st["A"], st["name"]
        reader = Reader(st["count"], A)
        regions = [(s, x) for s, x in st["read"] if len(s) >= SHORT]
        syms, xs = [s for s, _ in regions], [x for _, x in regions]
        codes = reader.codes(syms)
        rhos = [isolation(c, np.cumsum(c)) for c in codes]
        allc, allr = np.concatenate(codes), np.concatenate(rhos)
        places, width = len(allc), float(np.log(A))
        q = np.quantile(allc, [0.05, 0.5, 0.95])
        print("STREAM kind=%s name=%s A=%d count_places=%d read_places=%d regions=%d | news a place: mean=%.4f quantiles 0.05=%.4f 0.50=%.4f 0.95=%.4f | section ln A=%.4f, places at or past it=%.4f" % (
            kind, name, A, sum(len(r) for r in st["count"]), places, len(regions), float(allc.mean()), q[0], q[1], q[2], width, float((allc >= width).mean())))
        cbar = float(allc.mean())
        print("  ISOLATION share of places whose isolation is x sections or more (beside it c/(2x + c), news alike at every place): %s" % " ".join(
            "x=%g:%.4f(%.4f)" % (m, float((allr >= m * width).mean()), cbar / (2 * m * width + cbar)) for m in (0.25, 0.5, 1, 2, 4, 8, 16, 32)))
        sigma = {("width", law): width for law in LAWS}
        for law in ("O", "C", "A", "G", "P"):
            sigma[("epoch2", law)] = locate(law, codes, rhos, 2.0, 64.0 * width)
            sigma[("epoch6", law)] = locate(law, codes, rhos, 6.0, 64.0 * width)
        sigma[("epoch6", "W")] = width
        # the changes: label -> (copies' symbols, coordinates, tolerance)
        changes = {}
        made = [("start", begun_later, 0.0)] + [("insert%.2f" % r, inserted, r) for r in RATES] + [("flip%.2f" % r, flipped, r) for r in RATES]
        for ci, (label, fn, rate) in enumerate(made):
            rng = np.random.default_rng([SEED, si, ci])
            # a made change is a change of places, so it is compared by place on every stream (a place's index its coordinate)
            idx = [np.arange(len(s), dtype=np.float64) for s, _ in regions]
            out = [fn(reader, s, x, rate, rng) for (s, _), x in zip(regions, idx)]
            changes[label] = ([o[0] for o in out], [o[1] for o in out], 0.25, float(FAR), 1.0, idx)
        for label, copy, tol in st["own"]:
            keep = [(s, x) for (s0, _), (s, x) in zip(st["read"], copy) if len(s0) >= SHORT]
            changes[label] = ([s for s, _ in keep], [x for _, x in keep], tol, st["far"], st["step"], xs)
        ccodes, crhos = {}, {}
        for label, (cs, cx, tol, far, step, xo) in changes.items():
            ccodes[label] = reader.codes(cs)
            crhos[label] = [isolation(c, np.cumsum(c)) if len(c) else np.zeros(0) for c in ccodes[label]]
            n = same = untouched = extra = 0
            for s, x, c, s2, x2, c2 in zip(syms, xo, codes, cs, cx, ccodes[label]):
                live = np.flatnonzero(np.isfinite(x2))
                if len(live) == 0:
                    continue
                dist, j = nearest(x[START + MARGIN:], x2[live])
                ok = dist <= tol
                j = live[j]
                n += len(dist)
                same += int((ok & (s2[j] == s[START + MARGIN:])).sum())
                untouched += int((ok & (np.abs(c2[j] - c[START + MARGIN:]) < 1e-9)).sum())
                extra += len(x2) - len(live)
            print("  CHANGE %s places compared=%d same=%.4f untouched=%.4f | the copy: places=%d of them inserted=%.4f news a place=%.4f tolerance=%g" % (
                label, n, same / max(n, 1), untouched / max(n, 1), sum(len(z) for z in cs), extra / max(sum(len(z) for z in cs), 1),
                float(np.concatenate(ccodes[label]).mean()), tol))
        for ext in extents:
            for law in LAWS:
                if ext != "epoch6" and law == "W":
                    continue
                sg = sigma[(ext, law)]
                if law == "G":
                    both = [claim(c, sg) for c in codes]
                    so, ro = [b[0] for b in both], [b[1] for b in both]
                else:
                    so = [sites_of(law, c, r, sg) for c, r in zip(codes, rhos)]
                n_sites = sum(len(z) for z in so)
                strides = np.concatenate([np.diff(np.cumsum(c)[z]) for c, z in zip(codes, so) if len(z) > 1]) / sg
                news = float(strides.sum())
                tail = " | strides in sections: mean=%.3f under 1=%.4f 2 or more=%.4f 3 or more=%.4f 5 or more=%.4f longest=%.1f; news in strides of 3 or more=%.4f" % (
                    float(strides.mean()), float((strides < 1 - 1e-12).mean()), float((strides >= 2).mean()), float((strides >= 3).mean()), float((strides >= 5).mean()),
                    float(strides.max()), float(strides[strides >= 3].sum()) / max(news, 1e-9))
                if law == "G":
                    rr = np.concatenate(ro)
                    tail += " | sites by round: 1=%.4f 2=%.4f 3=%.4f 4 or more=%.4f rounds=%d" % (
                        float((rr == 1).mean()), float((rr == 2).mean()), float((rr == 3).mean()), float((rr >= 4).mean()), int(rr.max()))
                print("  EXTENT %s law=%s sigma=%.4f sites=%d mean_epoch=%.3f%s" % (ext, law, sg, n_sites, places / max(n_sites, 1), tail))
                parts = []
                for label, (cs, cx, tol, far, step, xo) in changes.items():
                    acc = [0, 0, 0]
                    for i, (x, z, x2, c2, r2) in enumerate(zip(xo, so, cx, ccodes[label], crhos[label])):
                        if len(c2) == 0:
                            continue
                        kept, who, ch = compare(x, z, x2, sites_of(law, c2, r2, sg), tol, far, step)
                        acc[0] += int(kept.sum())
                        acc[1] += len(kept)
                        acc[2] += ch
                        if law == "G" and len(who):
                            rnd = ro[i][np.searchsorted(z, who)]
                            b = by_round.setdefault((ext, label), [0, 0, 0, 0])
                            b[0] += int(kept[rnd == 1].sum())
                            b[1] += int((rnd == 1).sum())
                            b[2] += int(kept[rnd > 1].sum())
                            b[3] += int((rnd > 1).sum())
                    parts.append("%s %s" % (label, show(acc)))
                    p = pooled.setdefault((ext, law, label), [0, 0, 0, 0, 0])
                    for j in range(3):
                        p[j] += acc[j]
                    if label == "start":
                        p[3] += places
                        p[4] += n_sites
                print("    KEPT %s law=%s | %s" % (ext, law, " | ".join(parts)))
        sys.stdout.flush()
    print("POOLED kind=%s over its %d streams, by sites" % (kind, len(streams)))
    labels = []
    for (_, _, label) in pooled:
        if label not in labels:
            labels.append(label)
    for ext in extents:
        for law in LAWS:
            if (ext, law, "start") not in pooled:
                continue
            p = pooled[(ext, law, "start")]
            print("  POOLED %s law=%s mean_epoch=%.3f | %s" % (ext, law, p[3] / max(p[4], 1), " | ".join(
                "%s %s" % (label, show(pooled[(ext, law, label)][:3])) for label in labels if (ext, law, label) in pooled)))
        for label in labels:
            if (ext, label) in by_round:
                b = by_round[(ext, label)]
                print("  ROUNDS %s %s: the claim's sites of round one kept=%.4f (%d), of later rounds kept=%.4f (%d)" % (
                    ext, label, b[0] / max(b[1], 1), b[1], b[2] / max(b[3], 1), b[3]))
    for ext in extents:
        for label in labels:
            if (ext, "P", label) in pooled and (ext, "C", label) in pooled:
                lp, lc = lift(*pooled[(ext, "P", label)][:3])[2], lift(*pooled[(ext, "C", label)][:3])[2]
                la = lift(*pooled[(ext, "A", label)][:3])[2]
                print("  RATIO %s %s: the first round's lift over the carried cut's=%.3f (%.4f over %.4f); the claim's in the order of arrival=%.4f" % (
                    ext, label, lp / max(lc, 1e-9), lp, lc, la))


# ---------------------------------------------------------------------------------------------------------------- boundaries
def made():
    """The instrument's dry run: the laws against their plain statements on made news, then a made stream read whole."""
    rng = np.random.default_rng(SEED)
    for trial in range(400):
        n = int(rng.integers(1, 40))
        c = np.round(rng.exponential(1.0, n) * 8) / 8 + 0.125 if trial % 2 else rng.integers(1, 4, n).astype(np.float64)  # dyadic: sums without rounding
        sigma = float(rng.choice([0.5, 1.0, 2.5, 6.0]))
        S = np.cumsum(c)
        greater = lambda u, t: c[u] > c[t] or (c[u] == c[t] and u < t)  # noqa: E731
        reach = lambda u, t: abs(S[u] - S[t]) < sigma  # noqa: E731
        plain_p = [t for t in range(n) if not any(greater(u, t) and reach(u, t) for u in range(n) if u != t)]
        plain_g = []
        for t in sorted(range(n), key=lambda t: (-c[t], t)):
            if not any(reach(u, t) for u in plain_g):
                plain_g.append(t)
        rho = isolation(c, S)
        p, (g, rounds) = np.flatnonzero(rho >= sigma), claim(c, sigma)
        assert p.tolist() == plain_p and g.tolist() == sorted(plain_g), (trial, c, sigma)
        assert g[rounds == 1].tolist() == plain_p and set(plain_p) <= set(plain_g)
        assert all(t in plain_p for t in range(n) if c[t] >= sigma)
        assert len(g) < 2 or float(np.diff(S[g]).min()) >= sigma
        assert set(np.flatnonzero(rho >= 2 * sigma).tolist()) <= set(plain_p)
        plain_a = []
        for t in range(n):
            if not any(reach(u, t) for u in plain_a):
                plain_a.append(t)
        a = arrival(c, sigma)
        assert a.tolist() == plain_a and (len(a) < 2 or float(np.diff(S[a]).min()) >= sigma)
        assert {0} | {t for t in range(n) if c[t] >= sigma} == {t for t in range(n) if not any(reach(u, t) for u in range(t))} <= set(plain_a)
        k = int(rng.integers(1, n + 1))
        c0 = np.concatenate([c[:k], [2.0 ** -30], c[k:]])
        keep = np.concatenate([np.arange(k), np.arange(k, n) + 1])
        assert (np.flatnonzero(isolation(c0, np.cumsum(c0)) >= sigma)).tolist() == keep[p].tolist() or abs(rho - sigma).min() < 1e-9
    print("CHECK 400 made regions: the first round and the claim equal their plain statements; round one is the first round; a place of a section or more opens; sites stand a section apart; the first round nests; a place of no news moves no site; the claim in the order of arrival equals its plain statement, its sites stand a section apart and its first round is the first place and the places of a section or more")
    A, V = 12, 12
    T = rng.dirichlet(np.full(V, 0.15), size=(V, V))

    def draw(n):
        s = [int(rng.integers(V)), int(rng.integers(V))]
        for _ in range(n - 2):
            s.append(int(rng.choice(V, p=T[s[-1], s[-2]])))
        return np.array(s, dtype=np.int64)

    count = [draw(4000) for _ in range(30)]
    regions = [draw(int(rng.integers(40, 900))) for _ in range(60)]
    own = [(s[3:], np.arange(3, len(s), dtype=np.float64)) for s in regions]
    read("made", [{"name": "made", "A": A, "count": count, "read": [(s, np.arange(len(s), dtype=np.float64)) for s in regions], "tol": 0.25, "far": float(FAR),
                   "step": 1.0, "own": [("begun3", own, 0.25)]}])


def spaces_doubled(sym, x):
    """Every line's leading spaces doubled."""
    n = len(sym)
    other = (sym != 32).astype(np.int64)
    first = np.concatenate([[True], sym[:-1] == 10])
    head = np.maximum.accumulate(np.where(first, np.arange(n), 0))
    cs = np.cumsum(other)
    lead = (sym == 32) & (cs - (cs[head] - other[head]) == 0)
    if not lead.any():
        return sym, x
    return insert_after(sym, x, lead, np.full(int(lead.sum()), 32, dtype=np.int64))


def octets(count_shard, held_shard, tools, count_mb, read_places):
    sys.path.insert(0, tools)
    import corpus_passage as cp

    def piece_of(title, text, s, e):
        head = title + b"\n" if s == 0 and title else b""
        return np.frombuffer(head + text[s:e], dtype=np.uint8).astype(np.int64)

    count, count_n = {n: [] for n in cp.NAMES}, dict.fromkeys(cp.NAMES, 0)
    for r in cp.rows_of(count_shard):
        name = cp.slice_of(r)
        if name is None or not r["text"] or count_n[name] >= count_mb * 1_000_000:
            continue
        for s, e in cp.runs_of(name, r["text"])[0]:
            count[name].append(piece_of(r["title"], r["text"], s, e))
            count_n[name] += len(count[name][-1])
    held, held_n, want = {n: [] for n in cp.NAMES}, dict.fromkeys(cp.NAMES, 0), dict.fromkeys(cp.NAMES, 128)
    for r in cp.rows_of(held_shard):
        name = cp.slice_of(r)
        if name is None or not want[name] or not r["text"]:
            continue
        runs = cp.runs_of(name, r["text"])[0]
        if not runs:
            continue
        for s, e in runs:
            if held_n[name] < read_places:
                held[name].append(piece_of(r["title"], r["text"], s, e)[: read_places - held_n[name]])
                held_n[name] += len(held[name][-1])
        want[name] -= 1
    streams = []
    for name in cp.NAMES:
        regions = [(s, np.arange(len(s), dtype=np.float64)) for s in held[name]]
        streams.append({"name": name, "A": 256, "count": count[name], "read": regions, "tol": 0.25, "far": float(FAR), "step": 1.0,
                        "own": [("spaces", [spaces_doubled(s, x) for s, x in regions], 0.25)]})
    read("octets", streams)


def arrivals(arr, raw, n_count):
    names = sorted(os.listdir(os.path.join(raw, "orig")))
    rec = np.dtype([("t", "<f8"), ("m", "<f8"), ("back", "<i4"), ("pad", "<i4")])

    def ring(kind, s):
        return [np.fromfile(os.path.join(arr, kind, "%s.a%d" % (n[:-4], s)), dtype=rec) for n in names]

    def word(v, turn, scale, off):
        """The ring word of G136 (the octave's step of |z| on the fixed grid; the interval against the ring's free turn, in
        quarter turns; each clipped to 3 either way: 49 states), for the arrivals 2 on, and their times in the original's."""
        t, m = v["t"], v["m"]
        if len(t) < 4:
            return np.zeros(0, dtype=np.int64), np.zeros(0)
        L = np.where(m < 1.0, 0, np.floor(np.log2(np.maximum(m, 1.0))).astype(np.int64) + 1)
        b = np.clip(np.diff(L)[1:], -3, 3).astype(np.int64)
        d = np.clip(np.rint(4.0 * np.diff(t)[1:] / turn) - 4, -3, 3).astype(np.int64)
        return (b + 3) * 7 + (d + 3), t[2:] * scale + off

    streams = []
    for s in range(3, 8):
        turn = float(1 << s)
        orig = [word(v, turn, 1.0, 0.0) for v in ring("orig", s)]
        third = [word(v, turn, 1.0, 112.0 / 3.0) for v in ring("third", s)][n_count:]
        fast = [word(v, turn / 2, 2.0, 0.0) for v in ring("fast", s - 1)][n_count:]
        streams.append({"name": "ring%d" % s, "A": 49, "count": [k for k, _ in orig[:n_count]], "read": orig[n_count:], "tol": 1e-6, "far": FAR * turn,
                        "step": turn, "own": [("third", third, turn / 2), ("fast", fast, turn / 2)]})
    read("arrivals", streams)


if __name__ == "__main__":
    if sys.argv[1] == "made":
        made()
    elif sys.argv[1] == "octets":
        octets(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6]))
    else:
        arrivals(sys.argv[2], sys.argv[3], int(sys.argv[4]))
