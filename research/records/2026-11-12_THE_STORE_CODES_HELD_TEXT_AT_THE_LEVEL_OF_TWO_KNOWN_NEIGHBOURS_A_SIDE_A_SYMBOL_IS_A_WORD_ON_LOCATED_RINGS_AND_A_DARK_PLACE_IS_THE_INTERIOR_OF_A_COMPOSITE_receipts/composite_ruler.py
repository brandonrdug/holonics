"""composite_ruler: what founding frequent runs as symbols of higher rank is worth at a fixed reach in symbols. A host
instrument: it enters no law (a merge table is a ruler's, never the machine's).

The question. The store's states code held text at the level of a count of each place's two nearest known neighbours a
side (neighbour_ruler.py). If the pairs of symbols that recur most were symbols themselves (composites: a character of
several bytes, a frequent run), a reach of two symbols would span more of the text. What does the code of the next symbol,
in nats a byte of the text, read at a reach of one, two and three symbols as the composites are founded?

The read. On the counts stream of neighbour_ruler.py (each slice's first COUNT_MB megabytes of
common_corpus_1/subset_1_1.parquet through the store's rule, a break symbol between pieces), composites are founded PASS
at a time: the adjacent pairs of byte or composite symbols counted, and the most frequent pairs taken greedily so that no
symbol is a first of one taken pair and a second of another (their occurrences then never overlap; a pair of one symbol
with itself is taken alone, left to right). The held role's first READ_PLACES places a slice are cut by the same pairs in
the same order. At each count of composites: the next symbol's code given the one, two and three symbols before it
(Witten-Bell backoff, counts from the cut counts stream), summed over the held symbols and divided by the held places
(nats a byte), with the mean bytes a symbol, the count of symbols the alphabet holds and the cells of each table.

usage: python3 -I composite_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES
Output: numbers only.
"""
import sys
import time

import numpy as np

count_shard, held_shard, tools, count_mb, read_places = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
sys.path.insert(0, tools)
import corpus_passage as cp  # noqa: E402

VOID, NEAR, HELD, A = 256, 5, 128, 257
t0 = time.time()


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
print("# composite_ruler counts<=%d MB a slice (common_corpus_1/subset_1_1.parquet), read: the held role's first %d places a slice; load_s=%.0f"
      % (count_mb, read_places, time.time() - t0))


BREAK, FIRST = 257, 258
PASS = 32
AT = (0, 64, 256, 1024, 2048)


def joined(pieces):
    out = []
    for p in pieces:
        out.append(p)
        out.append(np.array([BREAK], dtype=np.int64))
    return np.concatenate(out)


def cut(s, pairs):
    """Every occurrence of each taken pair (a, b, id) becomes id. The pairs of one pass never overlap."""
    if len(pairs) == 1 and pairs[0][0] == pairs[0][1]:
        a, _, new = pairs[0]
        eq = s == a
        hit = eq[:-1] & eq[1:]
        start = eq & ~np.concatenate([[False], eq[:-1]])
        run = np.cumsum(start) - 1
        first = np.flatnonzero(start)
        idx = np.flatnonzero(hit)
        idx = idx[(idx - first[run[idx]]) % 2 == 0]
    else:
        v = max(int(s.max()), max(max(a, b) for a, b, _ in pairs)) + 1
        table = np.zeros(v * v, dtype=np.int64)
        for a, b, new in pairs:
            table[a * v + b] = new
        got = table[s[:-1] * v + s[1:]]
        idx = np.flatnonzero(got)
        new = got[idx]
    keep = np.ones(len(s), dtype=bool)
    keep[idx + 1] = False
    out = s.copy()
    out[idx] = new
    return out[keep]


def take(s, next_id):
    """The pass's pairs: most frequent first, no symbol both a first and a second among them."""
    v = int(s.max()) + 1
    ok = (s[:-1] < 256) | (s[:-1] >= FIRST)
    ok &= (s[1:] < 256) | (s[1:] >= FIRST)
    c = np.bincount(s[:-1][ok] * v + s[1:][ok], minlength=v * v)
    order = np.argsort(c)[::-1][: 8 * PASS]
    a0, b0 = int(order[0]) // v, int(order[0]) % v
    if a0 == b0:
        return [(a0, b0, next_id)]
    firsts, seconds, pairs = set(), set(), []
    for k in order:
        a, b = int(k) // v, int(k) % v
        if c[k] < 2 or a == b or a in seconds or b in firsts:
            continue
        firsts.add(a)
        seconds.add(b)
        pairs.append((a, b, next_id + len(pairs)))
        if len(pairs) == PASS:
            break
    return pairs


def tables(s, v, order):
    key = s[order:].copy()
    ctx = np.zeros(len(s) - order, dtype=np.int64)
    for j in range(1, order + 1):
        ctx = ctx * v + s[order - j: len(s) - j]
    full, cnt = np.unique(ctx * v + key, return_counts=True)
    uctx, at, distinct = np.unique(full // v, return_index=True, return_counts=True)
    return full, cnt, uctx, np.add.reduceat(cnt, at), distinct


def read(train, held, v, reach):
    """Nats summed over the held symbols under each reach's Witten-Bell chain."""
    c0 = np.bincount(train, minlength=v).astype(np.float64)
    p = (c0[held] + 0.5) / (c0.sum() + 0.5 * v)
    sums, cells = [], []
    for order in range(1, reach + 1):
        full, cnt, uctx, tot, distinct = tables(train, v, order)
        ctx = np.zeros(len(held), dtype=np.int64)
        valid = np.arange(len(held)) >= order
        for j in range(1, order + 1):
            ctx = ctx * v + np.concatenate([np.zeros(j, dtype=np.int64), held[: len(held) - j]])
        k = ctx * v + held
        i = np.minimum(np.searchsorted(full, k), len(full) - 1)
        c = np.where(full[i] == k, cnt[i], 0).astype(np.float64)
        i = np.minimum(np.searchsorted(uctx, ctx), len(uctx) - 1)
        seen = (uctx[i] == ctx) & valid
        n, d = np.where(seen, tot[i], 0).astype(np.float64), np.where(seen, distinct[i], 0).astype(np.float64)
        p = np.where(seen, (c + d * p) / np.maximum(n + d, 1e-300), p)
        sums.append(float(-np.log(p).sum()))
        cells.append((len(uctx), len(full)))
    return sums, cells


for name in cp.NAMES:
    train, test = joined(count[name]), joined(held[name])
    places = sum(len(p) for p in held[name])
    founded, next_id = 0, FIRST
    print("COMPOSITE slice=%s counts_places=%d held_places=%d" % (name, sum(len(p) for p in count[name]), places), flush=True)
    for target in AT:
        while founded < target:
            pairs = take(train, next_id)[: target - founded]
            if not pairs:
                break
            train, test = cut(train, pairs), cut(test, pairs)
            founded += len(pairs)
            next_id += len(pairs)
        v = next_id
        sums, cells = read(train, test, v, 3)
        print("  composites=%-5d bytes_a_symbol counts=%.3f held=%.3f | nats a byte: reach1=%.4f reach2=%.4f reach3=%.4f | nats a symbol: reach2=%.4f | cells(contexts,pairs) reach1=%d,%d reach2=%d,%d reach3=%d,%d  s=%.0f" % (
            founded, sum(len(p) for p in count[name]) / (len(train) - len(count[name])), places / (len(test) - len(held[name])),
            sums[0] / places, sums[1] / places, sums[2] / places, sums[1] / (len(test) - len(held[name])),
            cells[0][0], cells[0][1], cells[1][0], cells[1][1], cells[2][0], cells[2][1], time.time() - t0), flush=True)
