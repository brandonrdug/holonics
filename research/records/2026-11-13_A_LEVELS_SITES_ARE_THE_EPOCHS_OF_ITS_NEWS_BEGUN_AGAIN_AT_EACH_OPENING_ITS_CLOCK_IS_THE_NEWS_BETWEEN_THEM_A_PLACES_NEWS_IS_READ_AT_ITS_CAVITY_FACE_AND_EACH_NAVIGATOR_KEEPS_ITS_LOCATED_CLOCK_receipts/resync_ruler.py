"""resync_ruler: whether a cut by carries keeps its sites when what stands before them changes, and what a written
place's stride may read (G124). A host instrument: it enters no law.

Codes, in nats, by Witten-Bell backoff on a counts stream: c0, c1, c2 of a held place with none, one and two symbols before
it known, and c2s with the symbol before and the symbol after known (backed off to c1's law).

Cuts, at a mean epoch of 6 places, the place whose stride carries OPENING its epoch, a piece's first place opening one:
  odometer    the stride is summed along the piece and a place opens where the sum crosses a multiple of one period (the
              remainder kept; the clock of news of October 27).
  restarting  the sum begins again at each opening: a place opens when the strides since the last opening, its own
              included, pass one period, and its stride begins the next sum.
Strides: the place's own code c2; c1 (a pair's form); c2s (one neighbour known a side); the symbol's class-mean c2; the
trained rates at state C. Each cut is read on c2: `code`, the opening places' mean code over the others'; `spread`, the
deviation over the mean of an epoch's summed c2 over the epochs whose every place is read; `screen`, the mean of
c1(t+1) - c2(t+1) at the opening places over the others'.

SHIFT. Each piece's sum is begun at an offset drawn evenly on one period (numpy's default generator, seed 124); for the
fixed packets the start is shifted by 1 to 5 places. `kept` is the share of the unshifted cut's openings, a piece's first
place left out, that the shifted cut also opens; `by opening` the same for a piece's second, third, fourth and later
openings.

STRETCH (the code slice). Every line's leading spaces are doubled, the codes are read again on the copy with the same
counts, and each cut keeps its own period. `kept` is the share of the original's openings, leading spaces and a piece's
first place left out, whose place opens in the copy.

With a SECTION in nats (G125) every stride that is a code is cut at that one section in place of the fitted period, the
trained rates are left out, and a cut's line gains `one`, the share of its whole epochs that are one place, and `fill`,
an epoch's mean news over the section.

usage: python3 -I resync_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES PACES [SECTION]
Output: numbers only.
"""
import sys
import time

import numpy as np

count_shard, held_shard, tools, count_mb, read_places, paces = (
    sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6])
section = float(sys.argv[7]) if len(sys.argv) > 7 else None
sys.path.insert(0, tools)
import corpus_passage as cp  # noqa: E402

VOID, BREAK, V, NEAR, HELD, MEAN = 256, 257, 258, 5, 128, 6
UNIT = 1_000_000
t0 = time.time()

# The pace table: a rate a symbol (bytes 0..255, the void at 256), on each paced head at each state, in millionths.
columns, rate, open_row, code_line = None, {}, {}, []
for line in open(paces):
    if line.startswith(("#", "CHECK", "SUMMARY")):
        continue
    f = line.rstrip("\n").split("\t")
    if f[0] == "class":
        columns = f[3:]
        rate = {c: np.zeros(257, dtype=np.int64) for c in columns}
        held_by_codec = np.zeros(257, dtype=bool)
        continue
    values = [int(round(float(x) * UNIT)) for x in f[3:]]
    if f[1] == "open":
        open_row = dict(zip(columns, values))
        continue
    sym = VOID if f[1] == "void" else int(f[1])
    held_by_codec[sym] = True
    if f[2] == "code_line" and f[1] != "void":
        code_line.append(sym)
    for c, x in zip(columns, values):
        rate[c][sym] = x
for c in columns:
    rate[c][~held_by_codec] = open_row[c]
code_line = np.array(code_line)
letters = np.array([b for b in code_line if chr(b).isalpha()])
print("# epoch_cut_ruler: paces of %d symbols the codec holds, %d of them the code line's bytes; columns %s" % (
    int(held_by_codec.sum()), len(code_line), " ".join(columns)))
for c in columns:
    r = rate[c][code_line] / UNIT
    print("PACES %s code_line: mean=%.3f spread=%.3f letters_mean=%.3f newline=%.3f space=%.3f | all bytes met later take their own" % (
        c, r.mean(), r.std(), rate[c][letters].mean() / UNIT, rate[c][10] / UNIT, rate[c][32] / UNIT))


def piece_of(title, text, s, e):
    opens, closes = s == 0, e == len(text)
    head = title + b"\n" if opens and title else b""
    sym = np.frombuffer(head + text[s:e], dtype=np.uint8).astype(np.int64)
    return np.concatenate([sym, np.full(NEAR, VOID, dtype=np.int64)]) if closes else sym


count = {name: [] for name in cp.NAMES}
count_n = dict.fromkeys(cp.NAMES, 0)
for row in cp.rows_of(count_shard):
    name = cp.slice_of(row)
    if name is None or not row["text"] or count_n[name] >= count_mb * 1_000_000:
        continue
    for s, e in cp.runs_of(name, row["text"])[0]:
        piece = piece_of(row["title"], row["text"], s, e)
        count[name].append(piece)
        count_n[name] += len(piece)
held = {name: [] for name in cp.NAMES}
held_n = dict.fromkeys(cp.NAMES, 0)
want = dict.fromkeys(cp.NAMES, HELD)
for row in cp.rows_of(held_shard):
    name = cp.slice_of(row)
    if name is None or not want[name] or not row["text"]:
        continue
    runs = cp.runs_of(name, row["text"])[0]
    if not runs:
        continue
    for s, e in runs:
        if held_n[name] < read_places:
            piece = piece_of(row["title"], row["text"], s, e)[: read_places - held_n[name]]
            held[name].append(piece)
            held_n[name] += len(piece)
    want[name] -= 1
print("# counts<=%d MB a slice, read: the held role's first %d places a slice; load_s=%.0f" % (count_mb, read_places, time.time() - t0))


def joined(pieces):
    out = []
    for p in pieces:
        out.append(p)
        out.append(np.array([BREAK], dtype=np.int64))
    return np.concatenate(out)



from bisect import bisect_right


def table(ctx, key):
    full, cnt = np.unique(ctx * V + key, return_counts=True)
    uctx, at, distinct = np.unique(full // V, return_index=True, return_counts=True)
    return full, cnt, uctx, np.add.reduceat(cnt, at), distinct


def backoff(tab, ctx, key, valid, lower):
    full, cnt, uctx, tot, distinct = tab
    k = ctx * V + key
    i = np.minimum(np.searchsorted(full, k), len(full) - 1)
    c = np.where(full[i] == k, cnt[i], 0).astype(np.float64)
    i = np.minimum(np.searchsorted(uctx, ctx), len(uctx) - 1)
    seen = (uctx[i] == ctx) & valid
    n, d = np.where(seen, tot[i], 0).astype(np.float64), np.where(seen, distinct[i], 0).astype(np.float64)
    return np.where(seen, (c + d * lower) / np.maximum(n + d, 1e-300), lower)


class Coder:
    def __init__(self, train):
        self.c0 = np.bincount(train, minlength=V).astype(np.float64)
        self.t1 = table(train[:-1], train[1:])
        self.t2 = table(train[1:-1] * V + train[:-2], train[2:])
        self.ts = table(train[:-2] * V + train[2:], train[1:-1])

    def codes(self, s):
        n = len(s)
        at = np.arange(n)
        p0 = (self.c0[s] + 0.5) / (self.c0.sum() + 0.5 * V)
        b1 = np.concatenate([[0], s[:-1]])
        b2 = np.concatenate([[0, 0], s[:-2]])
        a1 = np.concatenate([s[1:], [0]])
        p1 = backoff(self.t1, b1, s, at >= 1, p0)
        p2 = backoff(self.t2, b1 * V + b2, s, at >= 2, p1)
        ps = backoff(self.ts, b1 * V + a1, s, (at >= 1) & (at < n - 1), p1)
        return -np.log(p0), -np.log(p1), -np.log(p2), -np.log(ps)


class Strand:
    def __init__(self, s, coder):
        self.s = s
        self.c0, self.c1, self.c2, self.c2s = coder.codes(s)
        start = np.concatenate([[True], s[:-1] == BREAK])
        self.piece = np.cumsum(start) - 1
        self.starts = np.flatnonzero(start)
        self.pos = np.arange(len(s)) - self.starts[self.piece]
        self.byte = s < 256
        self.read = self.byte & (self.pos > 0)
        nxt_byte = np.concatenate([self.byte[1:], [False]])
        prv_byte = np.concatenate([[False], self.byte[:-1]])
        self.mid = self.byte & nxt_byte & prv_byte & (self.pos > 0)
        self.through = np.concatenate([self.c1[1:] - self.c2[1:], [0.0]])

    def of_symbols(self, tab):
        return np.where(self.s <= VOID, tab[np.minimum(self.s, VOID)], 0)

    def own(self, code):
        return np.where(self.s <= VOID, np.rint(code * UNIT).astype(np.int64), 0)

    def odometer(self, k, period, delta=None):
        total = np.cumsum(k)
        base = (total - k)[self.starts][self.piece]
        sigma = total - base + (0 if delta is None else delta[self.piece])
        return (self.pos == 0) | (sigma // period > (sigma - k) // period)

    def restarting(self, k, period, delta=None):
        p = np.cumsum(k).tolist()
        n, starts = len(p), self.starts.tolist()
        out = []
        for pi, s in enumerate(starts):
            e = starts[pi + 1] if pi + 1 < len(starts) else n
            i = s
            base = (p[s - 1] if s else 0) - (0 if delta is None else int(delta[pi]))
            while True:
                out.append(i)
                j = bisect_right(p, base + period, i + 1, e)
                if j >= e:
                    break
                i, base = j, p[j - 1]
        opens = np.zeros(n, dtype=bool)
        opens[out] = True
        return opens

    def fixed(self, shift=None):
        return (self.pos == 0) | ((self.pos + (0 if shift is None else shift[self.piece])) % MEAN == 0)

    def mean_epoch(self, opens):
        return self.byte.sum() / max(int((opens & self.byte).sum()), 1)

    def fit(self, cut, k):
        lo, hi = 1, 400 * UNIT
        while hi - lo > max(lo // 4000, 1):
            mid = (lo + hi) // 2
            if self.mean_epoch(cut(k, mid)) < MEAN:
                lo = mid
            else:
                hi = mid
        return min((lo, hi), key=lambda q: abs(self.mean_epoch(cut(k, q)) - MEAN))


KEYS = ("n_o", "th_o", "n_r", "th_r", "m_o", "c_o", "m_r", "c_r", "whole", "w_n", "w_sq", "bytes", "epochs", "one")


def sums(sl, opens):
    a, b = sl.mid & opens, sl.mid & ~opens
    ra, rb = sl.read & opens, sl.read & ~opens
    epoch = np.cumsum(opens) - 1
    whole = np.bincount(epoch) == np.bincount(epoch, weights=sl.read)
    nats = np.bincount(epoch, weights=np.where(sl.read, sl.c2, 0.0))[whole]
    one = int((np.bincount(epoch)[whole] == 1).sum())
    return dict(n_o=int(a.sum()), th_o=float(sl.through[a].sum()), n_r=int(b.sum()), th_r=float(sl.through[b].sum()),
                m_o=int(ra.sum()), c_o=float(sl.c2[ra].sum()), m_r=int(rb.sum()), c_r=float(sl.c2[rb].sum()),
                whole=len(nats), w_n=float(nats.sum()), w_sq=float((nats * nats).sum()),
                bytes=int(sl.byte.sum()), epochs=int((opens & sl.byte).sum()), one=one)


def line(tag, r, extra=""):
    mean = r["w_n"] / max(r["whole"], 1)
    spread = max(r["w_sq"] / max(r["whole"], 1) - mean * mean, 0.0) ** 0.5 / max(mean, 1e-300)
    print("  CUT %-26s %s mean_epoch=%.3f code=%.4f spread=%.4f epoch_nats=%.3f screen=%.4f" % (
        tag, extra, r["bytes"] / max(r["epochs"], 1), (r["c_o"] / max(r["m_o"], 1)) / (r["c_r"] / max(r["m_r"], 1)), spread, mean,
        (r["th_o"] / max(r["n_o"], 1)) / (r["th_r"] / max(r["n_r"], 1))) + (
        "" if section is None else " one=%.4f fill=%.4f" % (r["one"] / max(r["whole"], 1), mean / section)), flush=True)


def kept_line(tag, sl, opens, other, counts):
    """Share of `opens` (a piece's first place left out) that `other` opens too, whole and by the opening's rank in its piece."""
    a = opens & (sl.pos > 0)
    rank = np.cumsum(opens) - 1
    rank = rank - rank[sl.starts][sl.piece]
    c = counts.setdefault(tag, [0, 0] + [0] * 8)
    c[0] += int((a & other).sum())
    c[1] += int(a.sum())
    for q, m in enumerate((rank == 1, rank == 2, rank == 3, rank >= 4)):
        c[2 + 2 * q] += int((a & other & m).sum())
        c[3 + 2 * q] += int((a & m).sum())
    return c


def kept_print(head, tag, c):
    print("  %s %-26s kept=%.4f of %d | by opening: second=%.3f third=%.3f fourth=%.3f later=%.3f" % (
        head, tag, c[0] / max(c[1], 1), c[1], c[2] / max(c[3], 1), c[4] / max(c[5], 1), c[6] / max(c[7], 1), c[8] / max(c[9], 1)), flush=True)


def stretched(pieces):
    """Each piece with every line's leading spaces doubled; with it, for each original place, its place in the copy and
    whether it is a leading space."""
    copies, places, leading = [], [], []
    for p in pieces:
        space = p == 32
        first = np.concatenate([[True], p[:-1] == 10])
        before = np.concatenate([[0], np.cumsum(~space)[:-1]])
        at_line = np.maximum.accumulate(np.where(first, before, -1))
        lead = space & (before == at_line)
        reps = np.where(lead, 2, 1)
        copies.append(np.repeat(p, reps))
        places.append(np.cumsum(reps) - 1)
        leading.append(lead)
    return copies, places, leading


rng = np.random.default_rng(124)
pooled, shift_pooled = {}, {}
col = [c for c in columns if "_C_" in c]
for name in cp.NAMES:
    train = joined(count[name])
    coder = Coder(train)
    sl = Strand(joined(held[name]), coder)
    n_sym = np.bincount(sl.s[sl.read], minlength=V).astype(np.float64)
    c0 = np.bincount(train, minlength=V).astype(np.float64)
    unigram = -np.log((c0 + 0.5) / (c0.sum() + 0.5 * V))
    class_mean = np.where(n_sym > 0, np.bincount(sl.s[sl.read], weights=sl.c2[sl.read], minlength=V) / np.maximum(n_sym, 1), unigram)
    class_tab = np.rint(class_mean[: VOID + 1] * UNIT).astype(np.int64)
    print("RESYNC slice=%s held_read=%d pieces=%d mean c0=%.4f c1=%.4f c2=%.4f c2s=%.4f  s=%.0f" % (
        name, int(sl.read.sum()), len(sl.starts), sl.c0[sl.read].mean(), sl.c1[sl.read].mean(), sl.c2[sl.read].mean(), sl.c2s[sl.read].mean(),
        time.time() - t0), flush=True)
    strides = [("own", lambda s: s.own(s.c2)), ("pair c1", lambda s: s.own(s.c1)), ("two-sided c2s", lambda s: s.own(s.c2s)),
               ("class", lambda s: s.of_symbols(class_tab))] + [(c, (lambda c: lambda s: s.of_symbols(rate[c]))(c)) for c in col]
    cuts = {}
    r = sums(sl, sl.fixed())
    line("fixed 6", r)
    pooled["fixed 6"] = {k: pooled["fixed 6"][k] + r[k] for k in KEYS} if "fixed 6" in pooled else r
    for tag, make in strides:
        k = make(sl)
        for kind, cut in (("odometer", sl.odometer), ("restarting", sl.restarting)):
            if kind == "odometer" and tag not in ("own",) + tuple(col):
                continue
            if section is not None and tag in col:
                continue
            period = sl.fit(cut, k) if section is None else int(round(section * UNIT))
            opens = cut(k, period)
            full = "%s %s" % (kind, tag)
            cuts[full] = (make, kind, period, opens)
            r = sums(sl, opens)
            line(full, r, "period=%.3f" % (period / UNIT))
            pooled[full] = {q: pooled[full][q] + r[q] for q in KEYS} if full in pooled else r
    # SHIFT
    for full, (make, kind, period, opens) in cuts.items():
        k = make(sl)
        delta = rng.integers(0, period, size=len(sl.starts))
        other = (sl.odometer if kind == "odometer" else sl.restarting)(k, period, delta)
        kept_line(full, sl, opens, other, shift_pooled)
    kept_line("fixed 6", sl, sl.fixed(), sl.fixed(rng.integers(1, MEAN, size=len(sl.starts))), shift_pooled)
    # STRETCH, the code slice
    if name == "code":
        copies, places, leading = stretched(held[name])
        cs = Strand(joined(copies), coder)
        off_o = np.concatenate([[0], np.cumsum([len(p) + 1 for p in held[name]])[:-1]])
        off_c = np.concatenate([[0], np.cumsum([len(p) + 1 for p in copies])[:-1]])
        to = np.zeros(len(sl.s), dtype=np.int64)
        lead = np.zeros(len(sl.s), dtype=bool)
        for q, (pl, ld) in enumerate(zip(places, leading)):
            to[off_o[q]: off_o[q] + len(pl)] = off_c[q] + pl
            lead[off_o[q]: off_o[q] + len(ld)] = ld
            to[off_o[q] + len(pl)] = off_c[q] + len(copies[q])
        assert (cs.s[to] == sl.s).all()
        added = np.ones(len(cs.s), dtype=bool)
        added[to] = False
        print("  STRETCH code: places %d to %d (added %d, %.4f of the copy); mean c2 of an added space %.4f, of an original leading space %.4f, of the other read places %.4f to %.4f in the copy" % (
            len(sl.s), len(cs.s), int(added.sum()), added.mean(), cs.c2[added].mean(), sl.c2[lead].mean(),
            sl.c2[sl.read & ~lead].mean(), cs.c2[to][sl.read & ~lead].mean()), flush=True)
        consider = (sl.pos > 0) & ~lead & sl.byte
        stretch = {}

        def stretch_line(tag, opens, copy_opens):
            a = opens & consider
            print("  STRETCH %-26s kept=%.4f of %d" % (tag, float(copy_opens[to][a].mean()), int(a.sum())), flush=True)

        stretch_line("fixed 6", sl.fixed(), cs.fixed())
        for full, (make, kind, period, opens) in cuts.items():
            k = make(cs)
            if "class" in full:
                k = cs.of_symbols(class_tab)
            stretch_line(full, opens, (cs.odometer if kind == "odometer" else cs.restarting)(k, period))
print("RESYNC pooled over the five slices (%s)" % ("each its own period" if section is None else "one section, %.4f nats" % section))
for tag, r in pooled.items():
    line(tag, r)
for tag, c in shift_pooled.items():
    kept_print("SHIFT", tag, c)
