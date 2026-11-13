"""screen_ruler: what the store's trained strides hold (a symbol's length, or how much it screens the place before it from
the place after it), and which cut of public held text screens (G123). A host instrument: it enters no law.

Codes. A held place's code with none, one and two symbols before it known, c0, c1, c2, in nats (Witten-Bell backoff on a
counts stream, as epoch_cut_ruler.py). through(t) = c1(t+1) - c2(t+1): the nats the place before t tells of the place after t
beyond what t tells, read where the three places are bytes of one piece. into(t) = c0(t) - c2(t): the nats the two places
before t tell of t.

Part A, by symbol. A symbol's transmission on the held places is the sum of through over the sum of c1(t+1), over the held
places where it stands. RANK lines: over the code line's bytes with 100 or more read places, the rank correlation of a
trained rate with minus that transmission, with minus the mean through, with the unigram length and with the class-mean
code. OPAQUE lines list the bytes of least and most transmission.

Part B, cuts. Each cut sums a stride along a piece and a place whose stride carries the sum across a multiple of one period
OPENS an epoch (the paced moment's convention: a place's stride is the thickness of the gap before it). The period is the
one whose mean epoch stands nearest 6 places. Strides: fixed (every 6 places), the trained rates at state C, a symbol's
unigram length, its class-mean code, the place's own code c2, and `friction`: minus the log of the symbol's transmission
on the counts stream (plug-in conditional mutual information of the byte before and the byte after, the symbol given,
over the entropy of the byte after, Miller-Madow corrected, held in [0.01, 1]). For each cut: `screen`, the mean of
through at the opening places over its mean at the others; `into`, the same for into; `code`, the same for c2; `spread`,
the standard deviation over the mean of an epoch's summed c2 over the epochs whose every place is read; and the kinds of
byte that open.

usage: python3 -I screen_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES PACES
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
    """Nats of each held symbol given 0, 1, ..., reach symbols before it (Witten-Bell chain); a list of arrays."""
    c0 = np.bincount(train, minlength=V).astype(np.float64)
    p = (c0[test] + 0.5) / (c0.sum() + 0.5 * V)
    out = [-np.log(p)]
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
        out.append(-np.log(p))
    return out


def friction_of(train):
    """A symbol's transmission on the counts stream: I(before; after | symbol) / H(after | symbol), Miller-Madow corrected."""
    full, cnt, _, _, _ = tables(train, 2)
    y, c = full % V, full // V
    a, x = c // V, c % V
    ok = (a < 256) & (x < 256) & (y < 256)
    a, x, y, n = a[ok], x[ok], y[ok], cnt[ok].astype(np.float64)
    n_a = np.bincount(a, weights=n, minlength=V)
    n_ax = np.bincount(a * V + x, weights=n, minlength=V * V)
    n_ay = np.bincount(a * V + y, weights=n, minlength=V * V)
    mi = np.bincount(a, weights=n * np.log(n * n_a[a] / (n_ax[a * V + x] * n_ay[a * V + y])), minlength=V) / np.maximum(n_a, 1)
    k_xy = np.bincount(a, minlength=V).astype(np.float64)
    k_x = (n_ax.reshape(V, V) > 0).sum(axis=1)
    k_y = (n_ay.reshape(V, V) > 0).sum(axis=1)
    mi = mi - (k_xy - k_x - k_y + 1) / (2 * np.maximum(n_a, 1))
    q = n_ay.reshape(V, V) / np.maximum(n_a, 1)[:, None]
    h = -(np.where(q > 0, q * np.log(np.maximum(q, 1e-300)), 0.0)).sum(axis=1)
    share = np.clip(mi / np.maximum(h, 1e-9), 0.01, 1.0)
    share[n_a < 50] = np.median(share[n_a >= 50])
    return share, n_a


PUNCT = np.zeros(V, dtype=bool)
for b in range(33, 127):
    if not chr(b).isalnum():
        PUNCT[b] = True


def rank_correlation(x, y):
    rx, ry = np.argsort(np.argsort(x)).astype(np.float64), np.argsort(np.argsort(y)).astype(np.float64)
    rx, ry = rx - rx.mean(), ry - ry.mean()
    return float((rx * ry).sum() / max((rx * rx).sum() * (ry * ry).sum(), 1e-300) ** 0.5)


def show(b):
    return chr(b) if 32 < b < 127 else "x%02x" % b


class Slice:
    def __init__(self, name, train):
        self.name = name
        self.s = joined(held[name])
        self.c0, self.c1, self.c2 = codes(train, self.s)
        start = np.concatenate([[True], self.s[:-1] == BREAK])
        self.piece = np.cumsum(start) - 1
        first_at = np.flatnonzero(start)
        self.pos = np.arange(len(self.s)) - first_at[self.piece]
        self.byte = self.s < 256
        self.read = self.byte & (self.pos > 0)
        nxt_byte = np.concatenate([self.byte[1:], [False]])
        prv_byte = np.concatenate([[False], self.byte[:-1]])
        self.mid = self.byte & nxt_byte & prv_byte & (self.pos > 0)
        self.through = np.concatenate([self.c1[1:] - self.c2[1:], [0.0]])
        self.next1 = np.concatenate([self.c1[1:], [0.0]])
        self.into = self.c0 - self.c2

    def of_symbols(self, table):
        return np.where(self.s <= VOID, table[np.minimum(self.s, VOID)], 0)

    def stride_opens(self, k, period):
        total = np.cumsum(k)
        base = (total - k)[np.flatnonzero(self.pos == 0)][self.piece]
        sigma = total - base
        return (self.pos == 0) | (sigma // period > (sigma - k) // period)

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


KEYS = ("n_o", "th_o", "n_r", "th_r", "m_o", "in_o", "c_o", "m_r", "in_r", "c_r", "whole", "w_n", "w_sq", "bytes", "epochs",
        "k_nl", "k_sp", "k_pu", "k_up", "k_lo", "k_di", "k_hi")


def sums(sl, opens):
    a, b = sl.mid & opens, sl.mid & ~opens
    ra, rb = sl.read & opens, sl.read & ~opens
    epoch = np.cumsum(opens) - 1
    whole = np.bincount(epoch) == np.bincount(epoch, weights=sl.read)
    nats = np.bincount(epoch, weights=np.where(sl.read, sl.c2, 0.0))[whole]
    o = sl.s[ra]
    return dict(n_o=int(a.sum()), th_o=float(sl.through[a].sum()), n_r=int(b.sum()), th_r=float(sl.through[b].sum()),
                m_o=int(ra.sum()), in_o=float(sl.into[ra].sum()), c_o=float(sl.c2[ra].sum()),
                m_r=int(rb.sum()), in_r=float(sl.into[rb].sum()), c_r=float(sl.c2[rb].sum()),
                whole=len(nats), w_n=float(nats.sum()), w_sq=float((nats * nats).sum()),
                bytes=int(sl.byte.sum()), epochs=int((opens & sl.byte).sum()),
                k_nl=int((o == 10).sum()), k_sp=int((o == 32).sum()), k_pu=int(PUNCT[o].sum()),
                k_up=int(((o >= 65) & (o <= 90)).sum()), k_lo=int(((o >= 97) & (o <= 122)).sum()),
                k_di=int(((o >= 48) & (o <= 57)).sum()), k_hi=int((o >= 128).sum()))


def line(tag, r, extra=""):
    mean = r["w_n"] / max(r["whole"], 1)
    spread = max(r["w_sq"] / max(r["whole"], 1) - mean * mean, 0.0) ** 0.5 / max(mean, 1e-300)
    ratio = lambda xo, no, xr, nr: (r[xo] / max(r[no], 1)) / (r[xr] / max(r[nr], 1))
    m = max(r["m_o"], 1)
    print("  %-22s %s mean_epoch=%.3f screen=%.4f (through at openings %.4f, others %.4f) into=%.4f code=%.4f spread=%.4f | opens: newline=%.3f space=%.3f punct=%.3f upper=%.3f lower=%.3f digit=%.3f high=%.3f" % (
        tag, extra, r["bytes"] / max(r["epochs"], 1), ratio("th_o", "n_o", "th_r", "n_r"), r["th_o"] / max(r["n_o"], 1), r["th_r"] / max(r["n_r"], 1),
        ratio("in_o", "m_o", "in_r", "m_r"), ratio("c_o", "m_o", "c_r", "m_r"), spread,
        r["k_nl"] / m, r["k_sp"] / m, r["k_pu"] / m, r["k_up"] / m, r["k_lo"] / m, r["k_di"] / m, r["k_hi"] / m), flush=True)


pooled = {}
for name in cp.NAMES:
    train = joined(count[name])
    sl = Slice(name, train)
    share_counts, n_counts = friction_of(train)
    c0 = np.bincount(train, minlength=V).astype(np.float64)
    unigram = -np.log((c0 + 0.5) / (c0.sum() + 0.5 * V))
    n_sym = np.bincount(sl.s[sl.read], minlength=V).astype(np.float64)
    class_mean = np.where(n_sym > 0, np.bincount(sl.s[sl.read], weights=sl.c2[sl.read], minlength=V) / np.maximum(n_sym, 1), unigram)
    n_mid = np.bincount(sl.s[sl.mid], minlength=V).astype(np.float64)
    th_sum = np.bincount(sl.s[sl.mid], weights=sl.through[sl.mid], minlength=V)
    nx_sum = np.bincount(sl.s[sl.mid], weights=sl.next1[sl.mid], minlength=V)
    held_share = th_sum / np.maximum(nx_sum, 1e-9)
    held_mean = th_sum / np.maximum(n_mid, 1)
    print("SCREEN slice=%s held_read=%d mid_places=%d mean c0=%.4f c1=%.4f c2=%.4f mean_through=%.4f transmission=%.4f  s=%.0f" % (
        name, int(sl.read.sum()), int(sl.mid.sum()), sl.c0[sl.read].mean(), sl.c1[sl.read].mean(), sl.c2[sl.read].mean(),
        sl.through[sl.mid].mean(), sl.through[sl.mid].sum() / sl.next1[sl.mid].sum(), time.time() - t0), flush=True)
    kinds = (("newline", sl.s == 10), ("space", sl.s == 32), ("lower", (sl.s >= 97) & (sl.s <= 122)), ("upper", (sl.s >= 65) & (sl.s <= 90)),
             ("digit", (sl.s >= 48) & (sl.s <= 57)), ("punct", PUNCT[sl.s]), ("high", (sl.s >= 128) & (sl.s < 256)))
    print("  KIND code c2 | transmission | into: " + " ".join("%s=%.3f|%.3f|%.3f" % (
        k, sl.c2[sl.read & m].mean() if (sl.read & m).any() else 0.0,
        sl.through[sl.mid & m].sum() / max(sl.next1[sl.mid & m].sum(), 1e-9),
        sl.into[sl.read & m].mean() if (sl.read & m).any() else 0.0) for k, m in kinds), flush=True)
    often = code_line[(n_sym[code_line] >= 100) & (n_mid[code_line] >= 50)]
    for c in columns:
        if "_C_" not in c:
            continue
        print("  RANK %s over %d bytes: with minus transmission=%.3f with minus mean through=%.3f with minus counts transmission=%.3f | with unigram=%.3f with class_mean=%.3f" % (
            c, len(often), rank_correlation(rate[c][often], -held_share[often]), rank_correlation(rate[c][often], -held_mean[often]),
            rank_correlation(rate[c][often], -share_counts[often]),
            rank_correlation(rate[c][often], unigram[often]), rank_correlation(rate[c][often], class_mean[often])), flush=True)
    print("  RANK transmission with unigram=%.3f with class_mean=%.3f; held with counts transmission=%.3f" % (
        rank_correlation(held_share[often], unigram[often]), rank_correlation(held_share[often], class_mean[often]),
        rank_correlation(held_share[often], share_counts[often])), flush=True)
    order = often[np.argsort(held_share[often])]
    print("  OPAQUE least transmission: " + " ".join("%s=%.3f" % (show(b), held_share[b]) for b in order[:14]), flush=True)
    print("  OPAQUE most transmission:  " + " ".join("%s=%.3f" % (show(b), held_share[b]) for b in order[-14:]), flush=True)
    friction = np.rint(-np.log(share_counts[: VOID + 1]) * UNIT).astype(np.int64)
    cuts = [("fixed 6", sl.fixed(), "")]
    for c in columns:
        if "_C_" in c:
            period, opens = sl.stride(sl.of_symbols(rate[c]))
            cuts.append(("stride " + c, opens, "period=%.3f" % (period / UNIT)))
    for tag, k in (("unigram", sl.of_symbols(np.rint(unigram[: VOID + 1] * UNIT).astype(np.int64))),
                   ("class", sl.of_symbols(np.rint(class_mean[: VOID + 1] * UNIT).astype(np.int64))),
                   ("own", np.where(sl.s <= VOID, np.rint(sl.c2 * UNIT).astype(np.int64), 0)),
                   ("friction", sl.of_symbols(friction))):
        period, opens = sl.stride(k)
        cuts.append((tag, opens, "period=%.3f" % (period / UNIT)))
    for tag, opens, extra in cuts:
        r = sums(sl, opens)
        line(tag, r, extra)
        pooled[tag] = {k: pooled[tag][k] + r[k] for k in KEYS} if tag in pooled else r
print("SCREEN pooled over the five slices (each its own period)")
for tag, r in pooled.items():
    line(tag, r)
