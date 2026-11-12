"""symbol_word_ruler: which registers of a byte's own word carry what symbols share. A host instrument: it enters no law.

The question. The store's trainer gives every byte value its own class and its own rows (a character map). A byte is a
word: b = q·m + r, a residue r on a circle of m and a winding q (the carry). If the rows a symbol brings to its
neighbours were composed from its registers' rows (one row a residue, one a winding: m + ⌈256/m⌉ rows where the map
keeps 256), what would the composition cost in code, at each period m, and does the code's own word do better than the
same split of a scrambled map?

The read. Counts of a class and the class before it, N[b, x], over the counts stream of neighbour_ruler.py (each
slice's first COUNT_MB megabytes of common_corpus_1/subset_1_1.parquet through the store's rule); the code of a class
given the byte before it, nats a place, over the held role's first READ_PLACES places a slice (rebuilt from
common_corpus_10/subset_100_10.parquet), under:
  order0     the slice's class counts (add one half);
  map        the full map, p(x | b) (Witten-Bell toward order0): 256 rows;
  word(m)    no three-way term between the residue, the winding and the class: log p(q, r, x) = α(q, r) + β(q, x) + γ(r, x),
             fitted to the counts by iterative proportional fitting (the margins (q, r), (q, x), (r, x)): m + ⌈256/m⌉ rows;
  foil(m)    the same fit after the byte values the slice's counts met are scrambled among themselves (the support kept, so
             the registers hold as many met bytes as the code's own): the mean of FOILS fixed permutations with their least
             and greatest; `foil256` is the first version's scramble over all 256 values, which spreads the met bytes over
             more registers than the code does and is kept only as that reading;
  crt(m1, m2, ...)  coprime residues in place of residue and winding: the registers b mod m_k, their product at least 256, so a
             byte is the one address its residues share (atlas radix.residue-address);
  both(m)    the class composed as well: no term above pairs between a register of the byte and a register of the class,
             log p(b, x) = a(b) + c(x) + sum over registers (R of b, T of x) of t(R, T): (m + ceil(256/m))^2 cells where the
             map keeps 256 * 257;
  bits       no term above pairs between the byte's eight binary digits and the class (margins (b), (bit_i, x)): 16 rows;
  residue(m), winding(m)   one register alone, p(x | r) and p(x | q).
A fall of word(m) under foil(m) is what the code's own arithmetic carries at period m; map − word(m) is the three-body
remainder a composition of two registers leaves (atlas code.pair-contact-conditional).

usage: python3 -I symbol_word_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES
Output: numbers only.
"""
import sys
import time

import numpy as np

count_shard, held_shard, tools, count_mb, read_places = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
sys.path.insert(0, tools)
import corpus_passage as cp  # noqa: E402

VOID, NEAR, HELD, A = 256, 5, 128, 257
PERIODS = (2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 20, 24, 26, 32, 40, 48, 64, 96, 128)
t0 = time.time()


def piece_of(title, text, s, e):
    opens, closes = s == 0, e == len(text)
    head = title + b"\n" if opens and title else b""
    sym = np.frombuffer(head + text[s:e], dtype=np.uint8).astype(np.int64)
    return np.concatenate([sym, np.full(NEAR, VOID, dtype=np.int64)]) if closes else sym


def pairs_of(stream_pieces):
    """Counts N[b, x] of a class x after a byte b, within pieces."""
    n = np.zeros((256, A))
    for sym in stream_pieces:
        prev, cur = sym[:-1], sym[1:]
        keep = prev < 256
        np.add.at(n, (prev[keep], cur[keep]), 1.0)
    return n


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
print("# symbol_word_ruler counts<=%d MB a slice (common_corpus_1/subset_1_1.parquet), read: the held role's first %d places a slice; load_s=%.0f"
      % (count_mb, read_places, time.time() - t0))


def fit(n, groups, sweeps=60):
    """The table on (b, x) with the byte's own margin and each register's margin with the class, and no higher term:
    iterative proportional fitting from the product of the byte's margin and the class's. `groups` maps a byte to its digit in each register."""
    m = np.outer(n.sum(1), n.sum(0)) / n.sum()
    targets = []
    for g in groups:
        t = np.zeros((g.max() + 1, A))
        np.add.at(t, g, n)
        targets.append(t)
    row = n.sum(1, keepdims=True)
    for _ in range(sweeps):
        for g, t in zip(groups, targets):
            have = np.zeros_like(t)
            np.add.at(have, g, m)
            m *= (t / np.maximum(have, 1e-300))[g]
        m *= row / np.maximum(m.sum(1, keepdims=True), 1e-300)
    return m / np.maximum(m.sum(1, keepdims=True), 1e-300)


def nats(p, h):
    """The held pairs' mean code under p(x | b)."""
    return float(-(h * np.log(np.maximum(p, 1e-300))).sum() / h.sum())


FOILS = 4
CRT = ((16, 17), (13, 20), (11, 24), (9, 29), (7, 37), (5, 7, 8), (5, 7, 9), (3, 7, 13), (3, 5, 7, 11), (2, 3, 5, 7, 11))


def fit_both(n, row_groups, col_groups, sweeps=60):
    """The table on (b, x) with the byte's margin, the class's margin and every (register of b, register of x) margin, no higher term."""
    m = np.outer(n.sum(1), n.sum(0)) / n.sum()
    pairs = [(gr, gc) for gr in row_groups for gc in col_groups]
    targets = []
    for gr, gc in pairs:
        t = np.zeros((gr.max() + 1, gc.max() + 1))
        np.add.at(t, (gr[:, None], gc[None, :]), n)
        targets.append(t)
    row, col = n.sum(1, keepdims=True), n.sum(0, keepdims=True)
    for _ in range(sweeps):
        for (gr, gc), t in zip(pairs, targets):
            have = np.zeros_like(t)
            np.add.at(have, (gr[:, None], gc[None, :]), m)
            m *= (t / np.maximum(have, 1e-300))[gr[:, None], gc[None, :]]
        m *= col / np.maximum(m.sum(0, keepdims=True), 1e-300)
        m *= row / np.maximum(m.sum(1, keepdims=True), 1e-300)
    return m / np.maximum(m.sum(1, keepdims=True), 1e-300)


rng = np.random.default_rng(20261112)
perm256 = rng.permutation(256)
for name in cp.NAMES:
    raw = pairs_of(count[name])
    met = np.flatnonzero(raw.sum(1) + raw.sum(0)[:256] > 0)
    perms = []
    for _ in range(FOILS):
        p = np.arange(256)
        p[met] = rng.permutation(met)
        perms.append(p)
    n = raw + 1e-3          # a thousandth of a count a cell keeps every margin positive (66 counts in all)
    h = pairs_of(held[name])
    base = (n.sum(0) + 0.5) / (n.sum() + 0.5 * A)
    distinct = (n > 0.5).sum(1, keepdims=True)
    full = (n + distinct * base) / (n.sum(1, keepdims=True) + distinct)
    full /= full.sum(1, keepdims=True)
    b = np.arange(256)
    xs = np.arange(A)
    line = ["WORD slice=%s counts_pairs=%d held_pairs=%d bytes_met=%d order0=%.4f map=%.4f(256 rows)" % (name, int(raw.sum()), int(h.sum()), len(met), nats(np.tile(base, (256, 1)), h), nats(full, h))]

    def foils(split):
        v = [nats(fit(n, split(p)), h) for p in perms]
        return "%.4f(%.4f..%.4f)" % (sum(v) / len(v), min(v), max(v))

    line.append("  bits=%.4f(16 rows) foil_bits=%s foil256_bits=%.4f" % (
        nats(fit(n, [(b >> i) & 1 for i in range(8)]), h), foils(lambda p: [(p >> i) & 1 for i in range(8)]), nats(fit(n, [(perm256 >> i) & 1 for i in range(8)]), h)))
    for m in PERIODS:
        q, r = b // m, b % m
        line.append("  m=%-3d rows=%-3d word=%.4f foil=%s foil256=%.4f residue=%.4f winding=%.4f" % (
            m, m + (255 // m + 1), nats(fit(n, [q, r]), h), foils(lambda p: [p // m, p % m]), nats(fit(n, [perm256 // m, perm256 % m]), h), nats(fit(n, [r]), h), nats(fit(n, [q]), h)))
    for ms in CRT:
        line.append("  crt%-16s rows=%-3d word=%.4f foil=%s" % (str(ms).replace(" ", ""), sum(ms), nats(fit(n, [b % k for k in ms]), h), foils(lambda p: [p % k for k in ms])))
    # two registers and a third: (4, 8, 8) = 2 + 3 + 3 binary digits, the columns of the 7-bit table and their halves
    for label, split in (("(4,8,8)", lambda p: [p >> 6, (p >> 3) & 7, p & 7]), ("(2,4,32)", lambda p: [p >> 7, (p >> 5) & 3, p & 31]), ("(4,4,16)", lambda p: [p >> 6, (p >> 4) & 3, p & 15])):
        g = split(b)
        line.append("  radix%-14s rows=%-3d word=%.4f foil=%s" % (label, sum(int(x.max()) + 1 for x in g), nats(fit(n, g), h), foils(split)))
    # the class composed as well (the void its own winding)
    for m in (16, 32):
        def both(p):
            px = np.concatenate([p, [256]])
            return nats(fit_both(n, [p // m, p % m], [np.where(xs < 256, px // m, 256 // m + (256 % m > 0)), np.where(xs < 256, px % m, 0)]), h)
        v = [both(p) for p in perms]
        line.append("  both m=%-3d cells=%-5d word=%.4f foil=%.4f(%.4f..%.4f)" % (m, (m + 255 // m + 1) * (m + 255 // m + 2), both(b), sum(v) / len(v), min(v), max(v)))
    def both_bits(p):
        px = np.concatenate([p, [0]])
        return nats(fit_both(n, [(p >> i) & 1 for i in range(8)], [(px >> i) & 1 for i in range(8)] + [(xs == 256).astype(np.int64)]), h)
    v = [both_bits(p) for p in perms]
    line.append("  both bits cells=%-5d word=%.4f foil=%.4f(%.4f..%.4f)" % (8 * 9 * 4, both_bits(b), sum(v) / len(v), min(v), max(v)))
    print("\n".join(line), "\n  s=%.0f" % (time.time() - t0), flush=True)
