"""epoch_cut_ruler: where the carries of the store's trained stride clocks cut public held text, read against a count
ruler's code of each place (R2 of G118). A host instrument: it enters no law.

The question. A paced head advances its clock at a place by its class's rate, kappa = 1 + c[u] (store_paces.txt, R1 of
G118: a row a class, the rate on each paced head at the store's states A and C). An epoch is the places between two
carries of sigma = sum |kappa| on a ring of one period. Do those carries fall where the text is bright (where a reader
that knows the two bytes before a place is surprised), so that a level above whose sites are epochs would open its sites
on the places that carry the news?

The read. Counts: each slice's first COUNT_MB megabytes of COUNT_SHARD through the store's rule for pieces (a title and a
newline before a piece that opens, NEAR void symbols after one that closes), a break symbol between pieces. Held: the held
role's first READ_PLACES places a slice, cut the same way. Each held place's code is -log p of its symbol given the two
symbols before it (Witten-Bell backoff on the counts stream, as composite_ruler.py's reach of two), in nats.

Cuts, each begun again at a piece's first place:
  stride   sigma is summed along the piece with the head's rates (a byte the codec does not hold takes the open row's);
           an epoch closes at each place where floor(sigma / period) rises, and the next place opens one. The period is the
           one whose mean epoch over the slice's byte places stands nearest 6 (the built packets' length).
  fixed    an epoch opens every 6 places (a cut blind to the text).
  code     an epoch opens at each place whose code stands at or over the level a sixth of the slice's byte places reach
           (the most a cut of that mean length can read).
  newline  an epoch opens after each newline (no control: it says how much of the stride cut is the line's).
  unigram  a stride cut whose stride is the symbol's order-zero code length on the counts stream (one constant a symbol).
  class    a stride cut whose stride is the mean two-back code of the symbol's held places (one constant a symbol).
  own      a stride cut whose stride is the place's own two-back code (the clock is the description length).
Both ends of an epoch are read. `ratio` is the mean code of the places that open an epoch over the mean code of the other
places; `carry` is the same for the places that close one (the place whose stride carried). Over byte places: a piece's
first place opens an epoch under every cut and has no bytes before it, so it is left out of every mean; void places are
left out too. `share` and `carry_share` are the parts of the read places' nats that the opening and the closing places
hold, `open` the part of the places that open. `after` is the part of a cut's opening places that follow a newline, a
space, other ASCII punctuation. `epoch_nats` is the mean of an epoch's summed code and `spread` its standard deviation
over that mean, over the epochs whose every place is read. `by position` is the mean code at an epoch's first, second, ...
place. KIND lines give the mean code and the share of read places by kind of byte; RANK lines the rank correlation, over
the code line's bytes with 100 or more read places, of a trained rate with the unigram length and with the class mean.

usage: python3 -I epoch_cut_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES PACES
Output: numbers only.
"""
import sys
import time

import numpy as np

count_shard, held_shard, tools, count_mb, read_places, paces = (
    sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6])
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


def tables(s, order):
    key = s[order:].copy()
    ctx = np.zeros(len(s) - order, dtype=np.int64)
    for j in range(1, order + 1):
        ctx = ctx * V + s[order - j: len(s) - j]
    full, cnt = np.unique(ctx * V + key, return_counts=True)
    uctx, at, distinct = np.unique(full // V, return_index=True, return_counts=True)
    return full, cnt, uctx, np.add.reduceat(cnt, at), distinct


def codes(train, test, reach=2):
    """Nats of each held symbol given the `reach` symbols before it (Witten-Bell chain down to the symbol's own count)."""
    c0 = np.bincount(train, minlength=V).astype(np.float64)
    p = (c0[test] + 0.5) / (c0.sum() + 0.5 * V)
    for order in range(1, reach + 1):
        full, cnt, uctx, tot, distinct = tables(train, order)
        ctx = np.zeros(len(test), dtype=np.int64)
        valid = np.arange(len(test)) >= order
        for j in range(1, order + 1):
            ctx = ctx * V + np.concatenate([np.zeros(j, dtype=np.int64), test[: len(test) - j]])
        k = ctx * V + test
        i = np.minimum(np.searchsorted(full, k), len(full) - 1)
        c = np.where(full[i] == k, cnt[i], 0).astype(np.float64)
        i = np.minimum(np.searchsorted(uctx, ctx), len(uctx) - 1)
        seen = (uctx[i] == ctx) & valid
        n, d = np.where(seen, tot[i], 0).astype(np.float64), np.where(seen, distinct[i], 0).astype(np.float64)
        p = np.where(seen, (c + d * p) / np.maximum(n + d, 1e-300), p)
    return -np.log(p)


PUNCT = np.zeros(V, dtype=bool)
for b in range(33, 127):
    if not chr(b).isalnum():
        PUNCT[b] = True


def rank_correlation(x, y):
    rx, ry = np.argsort(np.argsort(x)).astype(np.float64), np.argsort(np.argsort(y)).astype(np.float64)
    rx, ry = rx - rx.mean(), ry - ry.mean()
    return float((rx * ry).sum() / max((rx * rx).sum() * (ry * ry).sum(), 1e-300) ** 0.5)


class Slice:
    def __init__(self, name):
        self.name = name
        self.s = joined(held[name])
        self.code = codes(joined(count[name]), self.s)
        start = np.concatenate([[True], self.s[:-1] == BREAK])
        self.piece = np.cumsum(start) - 1
        first_at = np.flatnonzero(start)
        self.pos = np.arange(len(self.s)) - first_at[self.piece]
        self.byte = self.s < 256
        self.read = self.byte & (self.pos > 0)
        self.prev = np.concatenate([[BREAK], self.s[:-1]])

    def of_symbols(self, table):
        return np.where(self.s <= VOID, table[np.minimum(self.s, VOID)], 0)

    def stride_opens(self, k, period):
        total = np.cumsum(k)
        base = (total - k)[np.flatnonzero(self.pos == 0)][self.piece]
        sigma = total - base
        closes = sigma // period > (sigma - k) // period
        return (self.pos == 0) | np.concatenate([[False], closes[:-1]])

    def mean_epoch(self, opens):
        return self.byte.sum() / max(int((opens & self.byte).sum()), 1)

    def stride(self, k):
        lo, hi = 1, 400 * UNIT
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if self.mean_epoch(self.stride_opens(k, mid)) < MEAN:
                lo = mid
            else:
                hi = mid
        period = min((lo, hi), key=lambda p: abs(self.mean_epoch(self.stride_opens(k, p)) - MEAN))
        return period, self.stride_opens(k, period)

    def fixed(self):
        return self.pos % MEAN == 0

    def by_code(self):
        level = np.sort(self.code[self.byte])[::-1][int(self.byte.sum()) // MEAN - 1]
        return (self.code >= level) | (self.pos == 0)

    def after_newline(self):
        return (self.prev == 10) | (self.pos == 0)


def sums(sl, opens):
    """Counts and nats of the read places that open an epoch and of the others, and what the opening places follow."""
    a, b = sl.read & opens, sl.read & ~opens
    closes = np.concatenate([opens[1:], [True]])
    ca, cb = sl.read & closes, sl.read & ~closes
    epoch = np.cumsum(opens) - 1
    whole = np.bincount(epoch) == np.bincount(epoch, weights=sl.read)
    nats = np.bincount(epoch, weights=np.where(sl.read, sl.code, 0.0))[whole]
    prev = sl.prev[a]
    position = np.zeros(len(sl.s), dtype=np.int64)
    at = np.flatnonzero(opens)
    position = np.arange(len(sl.s)) - at[np.cumsum(opens) - 1]
    by_pos = [(int((sl.read & (position == j)).sum()), float(sl.code[sl.read & (position == j)].sum())) for j in range(9)]
    more = sl.read & (position >= 9)
    by_pos.append((int(more.sum()), float(sl.code[more].sum())))
    return dict(n_open=int(a.sum()), nats_open=float(sl.code[a].sum()), n_rest=int(b.sum()), nats_rest=float(sl.code[b].sum()),
                after_nl=int((prev == 10).sum()), after_sp=int((prev == 32).sum()), after_punct=int(PUNCT[prev].sum()),
                by_pos=by_pos, bytes=int(sl.byte.sum()), epochs=int((opens & sl.byte).sum()),
                n_carry=int(ca.sum()), nats_carry=float(sl.code[ca].sum()), n_stay=int(cb.sum()), nats_stay=float(sl.code[cb].sum()),
                whole=len(nats), whole_nats=float(nats.sum()), whole_squares=float((nats * nats).sum()))


def add(x, y):
    out = {k: x[k] + y[k] for k in x if k != "by_pos"}
    out["by_pos"] = [(a[0] + b[0], a[1] + b[1]) for a, b in zip(x["by_pos"], y["by_pos"])]
    return out


def line(tag, r, extra=""):
    mo, mr = r["nats_open"] / max(r["n_open"], 1), r["nats_rest"] / max(r["n_rest"], 1)
    n = max(r["n_open"], 1)
    mc, ms = r["nats_carry"] / max(r["n_carry"], 1), r["nats_stay"] / max(r["n_stay"], 1)
    mean = r["whole_nats"] / max(r["whole"], 1)
    spread = max(r["whole_squares"] / max(r["whole"], 1) - mean * mean, 0.0) ** 0.5 / max(mean, 1e-300)
    print("  %-22s %s mean_epoch=%.3f open=%.4f first=%.4f rest=%.4f ratio=%.4f share=%.4f | carry=%.4f carry_share=%.4f | epoch_nats=%.3f spread=%.4f | after newline=%.3f space=%.3f punct=%.3f" % (
        tag, extra, r["bytes"] / max(r["epochs"], 1), r["n_open"] / (r["n_open"] + r["n_rest"]), mo, mr, mo / mr,
        r["nats_open"] / (r["nats_open"] + r["nats_rest"]), mc / ms, r["nats_carry"] / (r["nats_carry"] + r["nats_stay"]),
        mean, spread, r["after_nl"] / n, r["after_sp"] / n, r["after_punct"] / n), flush=True)


def profile(tag, r):
    print("  %-22s by position: %s | 10+: %.3f (%d)" % (
        tag, " ".join("%.3f" % (x / max(c, 1)) for c, x in r["by_pos"][:9]), r["by_pos"][9][1] / max(r["by_pos"][9][0], 1), r["by_pos"][9][0]), flush=True)


pooled = {}
for name in cp.NAMES:
    sl = Slice(name)
    print("EPOCH slice=%s counts_places=%d held_places=%d read_places=%d mean_code=%.4f newline_share_of_bytes=%.5f  s=%.0f" % (
        name, sum(len(p) for p in count[name]), int(sl.byte.sum()), int(sl.read.sum()), sl.code[sl.read].mean(),
        (sl.s[sl.byte] == 10).mean(), time.time() - t0), flush=True)
    train = joined(count[name])
    c0 = np.bincount(train, minlength=V).astype(np.float64)
    unigram = -np.log((c0 + 0.5) / (c0.sum() + 0.5 * V))
    n_sym = np.bincount(sl.s[sl.read], minlength=V).astype(np.float64)
    class_mean = np.where(n_sym > 0, np.bincount(sl.s[sl.read], weights=sl.code[sl.read], minlength=V) / np.maximum(n_sym, 1), unigram)
    kinds = (("newline", sl.s == 10), ("space", sl.s == 32), ("lower", (sl.s >= 97) & (sl.s <= 122)), ("upper", (sl.s >= 65) & (sl.s <= 90)),
             ("digit", (sl.s >= 48) & (sl.s <= 57)), ("punct", PUNCT[sl.s]), ("high", (sl.s >= 128) & (sl.s < 256)))
    print("  KIND " + " ".join("%s=%.3f(%.4f)" % (k, sl.code[sl.read & m].mean() if (sl.read & m).any() else 0.0, (sl.read & m).sum() / sl.read.sum())
                               for k, m in kinds), flush=True)
    often = code_line[n_sym[code_line] >= 100]
    for c in columns:
        print("  RANK %s over %d bytes: with unigram=%.3f with class_mean=%.3f" % (
            c, len(often), rank_correlation(rate[c][often], unigram[often]), rank_correlation(rate[c][often], class_mean[often])), flush=True)
    cuts = []
    for c in columns:
        period, opens = sl.stride(sl.of_symbols(rate[c]))
        cuts.append(("stride " + c, opens, "period=%.3f" % (period / UNIT)))
    for tag, k in (("unigram", sl.of_symbols(np.rint(unigram[: VOID + 1] * UNIT).astype(np.int64))),
                   ("class", sl.of_symbols(np.rint(class_mean[: VOID + 1] * UNIT).astype(np.int64))),
                   ("own", np.where(sl.s <= VOID, np.rint(sl.code * UNIT).astype(np.int64), 0))):
        period, opens = sl.stride(k)
        cuts.append((tag, opens, "period=%.3f" % (period / UNIT)))
    cuts.append(("fixed 6", sl.fixed(), ""))
    cuts.append(("code", sl.by_code(), ""))
    cuts.append(("newline", sl.after_newline(), ""))
    for tag, opens, extra in cuts:
        r = sums(sl, opens)
        line(tag, r, extra)
        pooled[tag] = add(pooled[tag], r) if tag in pooled else r
    for tag, opens, _ in cuts:
        if tag != "newline":
            profile(tag, sums(sl, opens))
print("EPOCH pooled over the five slices (each its own period)")
for tag, r in pooled.items():
    line(tag, r)
for tag, r in pooled.items():
    if tag != "newline":
        profile(tag, r)
