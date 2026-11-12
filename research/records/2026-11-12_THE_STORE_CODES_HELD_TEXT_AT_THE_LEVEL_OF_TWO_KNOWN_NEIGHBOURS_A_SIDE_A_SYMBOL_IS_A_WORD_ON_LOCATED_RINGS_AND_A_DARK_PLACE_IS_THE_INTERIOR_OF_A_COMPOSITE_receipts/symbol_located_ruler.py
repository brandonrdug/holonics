"""symbol_located_ruler: what a symbol's address on a few rings is worth when the address is located from the counts, beside the
address read off its code point. A host instrument: it enters no law.

The question. symbol_word_ruler.py reads the registers of a byte's own code point (b = q·m + r, or its residues on coprime
moduli). Here each byte value met carries an address (r_1, ..., r_J), a residue on each of J rings of sizes (m_1, ..., m_J),
and the rows a symbol brings to its neighbour are its rings' rows at its residues (no term above pairs between a ring and the
class): p(x | b) ∝ Π_j F_j[r_j(b), x]. The address is located on the counts stream alone: the rows are fitted (iterative
proportional fitting), then each byte takes, on one ring at a time, the residue under which its own counts are coded least
(the other rings held), and the rows are fitted again, until no byte moves or ROUNDS rounds. Two starts: the byte's own word
(its code point's winding and residue, or its coprime residues), and a scramble of the met bytes.

The read: nats a place of a class given the byte before it, on the held role's first READ_PLACES places a slice, as in
symbol_word_ruler.py (order0 and the full map of 256 rows beside). `cells` is the count of distinct addresses the met bytes
hold (bytes that share every residue are one symbol to a neighbour).

usage: python3 -I symbol_located_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES [RING_SETS]
RING_SETS, when given, replaces the ring sets read: sets apart by ";", a set's sizes by "," ("16,27;9,32;4,7,9").
The helix's own towers at the alphabet (dyadic 2, 4, 8, ... and triadic 3, 9, 27, ...; `ring_periods`) were read with
"16,27;9,32;4,7,9;5,7,8;3,4,5,7;2,3,5,7,11" (symbol_located_ruler_towers.txt).
With RING_SETS given, a set of two rings also prints `cross`, a control with no location: the m_1 + m_2 - 2 most frequent
bytes each alone on a cell of the cross (a residue 0 on one ring), where a cell's row is free, and every other byte on the
cross's last cell, one row for all of them; `cross_bytes` is their count and `cross_mass` their share of the counts' places.
It says how much of a located address's share is a frequent byte keeping a row of its own (symbol_located_ruler.txt was
written before the control existed and has no such column).
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
print("# symbol_located_ruler counts<=%d MB a slice (common_corpus_1/subset_1_1.parquet), read: the held role's first %d places a slice; load_s=%.0f"
      % (count_mb, read_places, time.time() - t0))


ROUNDS = 40
RINGS = ((8, 32), (16, 17), (5, 7), (7, 9), (3, 5, 7), (5, 7, 9), (11, 13))
if len(sys.argv) > 6:
    RINGS = tuple(tuple(int(m) for m in ring_set.split(",")) for ring_set in sys.argv[6].split(";"))


def nats(p, h):
    return float(-(h * np.log(np.maximum(p, 1e-300))).sum() / h.sum())


def rows_of_address(n, groups, sizes, logf=None, sweeps=30):
    """The rings' rows under an address: log F_j (size_j × A) with p(x | b) = softmax_x Σ_j log F_j[g_j(b), x]."""
    if logf is None:
        logf = [np.zeros((s, A)) for s in sizes]
        logf[0] += np.log(n.sum(0) / n.sum())[None, :]
    targets = []
    for g, s in zip(groups, sizes):
        t = np.zeros((s, A))
        np.add.at(t, g, n)
        targets.append(t)
    row = n.sum(1, keepdims=True)
    for _ in range(sweeps):
        for j, (g, s) in enumerate(zip(groups, sizes)):
            logit = sum(f[gg] for f, gg in zip(logf, groups))
            logit -= logit.max(1, keepdims=True)
            p = np.exp(logit)
            p /= p.sum(1, keepdims=True)
            have = np.zeros((s, A))
            np.add.at(have, g, row * p)
            logf[j] += np.where(targets[j] > 0, np.log(np.maximum(targets[j], 1e-300) / np.maximum(have, 1e-300)), 0.0)
    return logf


def table_of(logf, groups):
    logit = sum(f[g] for f, g in zip(logf, groups))
    logit -= logit.max(1, keepdims=True)
    p = np.exp(logit)
    return p / p.sum(1, keepdims=True)


def locate(n, met, groups, sizes):
    """Each met byte takes, a ring at a time, the residue that codes its own counts least; rows refitted between."""
    groups = [g.copy() for g in groups]
    logf = rows_of_address(n, groups, sizes)
    rounds, moved_last = 0, -1
    for rounds in range(1, ROUNDS + 1):
        moved = 0
        for j, s in enumerate(sizes):
            rest = sum(f[g] for k, (f, g) in enumerate(zip(logf, groups)) if k != j)          # 256 × A
            gain = n @ logf[j].T                                                              # 256 × s
            z = rest[:, :, None] + logf[j].T[None, :, :]                                      # 256 × A × s
            top = z.max(1, keepdims=True)
            gain -= n.sum(1, keepdims=True) * (top[:, 0, :] + np.log(np.exp(z - top).sum(1)))
            best = gain.argmax(1)
            change = met[best[met] != groups[j][met]]
            moved += len(change)
            groups[j][change] = best[change]
            logf = rows_of_address(n, groups, sizes, logf, sweeps=8)
        moved_last = moved
        if moved == 0:
            break
    logf = rows_of_address(n, groups, sizes, logf, sweeps=30)
    return groups, logf, rounds, moved_last


rng = np.random.default_rng(20261112)
for name in cp.NAMES:
    raw = pairs_of(count[name])
    met = np.flatnonzero(raw.sum(1) > 0)
    n = raw + 1e-3
    h = pairs_of(held[name])
    base = (n.sum(0) + 0.5) / (n.sum() + 0.5 * A)
    distinct = (n > 0.5).sum(1, keepdims=True)
    full = (n + distinct * base) / (n.sum(1, keepdims=True) + distinct)
    full /= full.sum(1, keepdims=True)
    b = np.arange(256)
    scr = np.arange(256)
    scr[met] = rng.permutation(met)
    print("LOCATED slice=%s counts_pairs=%d held_pairs=%d bytes_met=%d order0=%.4f map=%.4f(256 rows)" % (
        name, int(raw.sum()), int(h.sum()), len(met), nats(np.tile(base, (256, 1)), h), nats(full, h)), flush=True)
    for sizes in RINGS:
        if len(sizes) == 2 and sizes[0] * sizes[1] == 256:
            word = lambda p: [p // sizes[1], p % sizes[1]]           # winding and residue at the period
        else:
            word = lambda p: [p % s for s in sizes]                 # coprime residues
        out = ["  rings=%-9s rows=%-3d" % (str(sizes).replace(" ", ""), sum(sizes))]
        for label, start in (("own_word", word(b)), ("scramble", word(scr))):
            given = nats(table_of(rows_of_address(n, start, sizes), start), h)
            groups, logf, rounds, moved = locate(n, met, start, sizes)
            cells = len({tuple(int(g[x]) for g in groups) for x in met})
            out.append("%s: given=%.4f located=%.4f (rounds=%d, last_moved=%d, cells=%d)" % (label, given, nats(table_of(logf, groups), h), rounds, moved, cells))
        if len(sys.argv) > 6 and len(sizes) == 2:
            cells_of_cross = [(0, 0)] + [(i, 0) for i in range(1, sizes[0])] + [(0, j) for j in range(1, sizes[1])]
            by_count = met[np.argsort(-raw.sum(1)[met], kind="stable")]
            own = len(cells_of_cross) - 1
            cross = [np.full(256, cells_of_cross[-1][k], dtype=np.int64) for k in range(2)]
            for rank, x in enumerate(by_count[:own]):
                cross[0][x], cross[1][x] = cells_of_cross[rank]
            out.append("cross: given=%.4f (cross_bytes=%d, cross_mass=%.4f)" % (
                nats(table_of(rows_of_address(n, cross, sizes), cross), h), own, raw.sum(1)[by_count[:own]].sum() / raw.sum()))
        print("  ".join(out), " s=%.0f" % (time.time() - t0), flush=True)
