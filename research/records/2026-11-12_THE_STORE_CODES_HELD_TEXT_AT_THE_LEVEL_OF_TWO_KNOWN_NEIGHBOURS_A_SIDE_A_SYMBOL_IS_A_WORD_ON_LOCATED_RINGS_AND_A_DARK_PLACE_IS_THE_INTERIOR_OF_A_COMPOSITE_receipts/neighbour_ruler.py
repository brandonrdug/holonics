"""neighbour_ruler: a count ruler for the store's held reads. A host instrument: it enters no law and no machine.

What it reads. Two public shards of PleIAs/common_corpus (revision 307910e4), through the store's own rule
(tools/corpus_passage.py: SLICES, runs_of, the held documents taken as `build` takes them):
  counts  the first shard the store's training read took (common_corpus_1/subset_1_1.parquet), each slice's pieces in
          the store's order, the first COUNT_MB megabytes of a slice: text the pass met in its first 0.2 GB;
  read    the shard the store's held documents came from (common_corpus_10/subset_100_10.parquet): each slice's first
          128 documents, as the store's held role holds them, the first READ_PLACES places of a slice (the held read's
          eight sections take about that many).
A piece is read as the trainer reads it: its title and one line feed where it opens its document with a title, its
text, and five voids where it closes one.

The law it copies from the pass (store_train.rs, field_train.rs `shape`): a stretch's context q and run a are each
4·2^o + u, o uniform on seven octaves, u uniform within the octave; a stretch that would leave under 4 places takes the
rest; a mask state opens each place with odds τ = u², u uniform, over the whole stretch or past the context, at least
one place open. The draws are this ruler's own (numpy, seeded): the same law, not the pass's keyed draws, so a code
here carries a sampling error of about 0.01 nats against the pass's own places.

The rulers. A compared place's code under the ruler of reach R is the Witten-Bell count code of its class given the
places within R of it that the state knows (a place outside the stretch is unknown, as it is to a region), backed off by
dropping the farthest known place first (the right one at a tie) down to the slice's class counts (add one half).
Read beside it: the place after the context with the whole context known (the release's first place) under left
contexts of 1 to 5 places, which are upper readings of h_1 … h_5 (atlas code.register-content-by-distance); the places
at distance 2 and 3 past the context with nothing nearer known, under the two nearest known places; and each left
table's cells (its contexts and its pairs of a context and a class), the V of atlas code.capacity-price.

usage: python3 -I neighbour_ruler.py COUNT_SHARD HELD_SHARD REPO_TOOLS COUNT_MB READ_PLACES REACH
Output: numbers only (no document text, no identifier).
"""
import hashlib
import math
import sys
import time

import numpy as np

count_shard, held_shard, tools = sys.argv[1], sys.argv[2], sys.argv[3]
count_mb, read_places, reach = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
sys.path.insert(0, tools)
import corpus_passage as cp  # noqa: E402

VOID, BITS, NEAR, LEAST, OCTAVES, HELD = 256, 9, 5, 4, 7, 128
t0 = time.time()


def piece_of(title, text, s, e):
    """A piece as the trainer reads it, and whether it closes its document."""
    opens, closes = s == 0, e == len(text)
    head = title + b"\n" if opens and title else b""
    sym = np.frombuffer(head + text[s:e], dtype=np.uint8).astype(np.uint16)
    return (np.concatenate([sym, np.full(NEAR, VOID, dtype=np.uint16)]) if closes else sym), closes


# ---- the counts' streams: each slice's pieces in the count shard's row order, until COUNT_MB
count = {name: [] for name in cp.NAMES}
count_n = dict.fromkeys(cp.NAMES, 0)
for row in cp.rows_of(count_shard):
    name = cp.slice_of(row)
    if name is None or not row["text"] or count_n[name] >= count_mb * 1_000_000:
        continue
    for s, e in cp.runs_of(name, row["text"])[0]:
        piece, _ = piece_of(row["title"], row["text"], s, e)
        count[name].append(piece)
        count_n[name] += len(piece)

# ---- the read's pieces: the held role as `build` writes it (the first HELD documents a slice with a kept run)
held = {name: [] for name in cp.NAMES}
want = dict.fromkeys(cp.NAMES, HELD)
sha = {name: hashlib.sha256() for name in cp.NAMES}
octets = dict.fromkeys(cp.NAMES, 0)
for row in cp.rows_of(held_shard):
    name = cp.slice_of(row)
    if name is None or not want[name] or not row["text"]:
        continue
    runs = cp.runs_of(name, row["text"])[0]
    if not runs:
        continue
    for s, e in runs:
        body = (row["title"] if s == 0 else b"") + row["text"][s:e]
        sha[name].update(body)
        octets[name] += len(body)
        held[name].append(piece_of(row["title"], row["text"], s, e))
    want[name] -= 1
print("# neighbour_ruler counts<=%d MB a slice of common_corpus_1/subset_1_1.parquet; read: the first %d places a slice of the held role rebuilt from"
      % (count_mb, read_places))
print("# common_corpus_10/subset_100_10.parquet; reach %d; load_s=%.0f" % (reach, time.time() - t0))
for name in cp.NAMES:
    print("HELD_REBUILT slice=%s documents=%d pieces=%d octets=%d sha256=%s" % (name, HELD - want[name], len(held[name]), octets[name], sha[name].hexdigest()))


def table(sym, offsets):
    """Counts of (the classes at `offsets`, the class) over a stream: sorted keys with counts, each context's total and distinct classes."""
    lo, hi = max(0, -min(offsets)), max(0, max(offsets))
    n = len(sym) - lo - hi
    ctx = np.zeros(n, dtype=np.int64)
    for j, o in enumerate(offsets):
        ctx |= sym[lo + o: lo + o + n].astype(np.int64) << (BITS * j)
    keys, counts = np.unique((ctx << BITS) | sym[lo: lo + n].astype(np.int64), return_counts=True)
    uctx, start = np.unique(keys >> BITS, return_index=True)
    return keys, counts, uctx, np.add.reduceat(counts, start), np.diff(np.append(start, len(keys)))


def code(tables, base, chains, cls, ctxsym, pattern):
    """Nats at each place, from its class, the classes at the universe's offsets and its pattern of known offsets."""
    out = np.zeros(len(cls))
    for pat in np.unique(pattern):
        at = np.nonzero(pattern == pat)[0]
        c = cls[at].astype(np.int64)
        p = base[c]
        chain = chains[int(pat)]
        for depth in range(1, len(chain) + 1):
            offs = chain[:depth]
            keys, counts, uctx, total, distinct = tables[offs]
            ctx = np.zeros(len(at), dtype=np.int64)
            for j, o in enumerate(offs):
                ctx |= ctxsym[o][at].astype(np.int64) << (BITS * j)
            i = np.minimum(np.searchsorted(uctx, ctx), len(uctx) - 1)
            seen = uctx[i] == ctx
            n, t = np.where(seen, total[i], 0).astype(np.float64), np.where(seen, distinct[i], 0).astype(np.float64)
            full = (ctx << BITS) | c
            k = np.minimum(np.searchsorted(keys, full), len(keys) - 1)
            got = np.where(keys[k] == full, counts[k], 0).astype(np.float64)
            p = np.where(seen, (got + t * p) / np.maximum(n + t, 1), p)
        out[at] = -np.log(p)
    return out


def chain_of(universe, bits):
    """A pattern's known offsets, nearest first (the left before the right at equal distance): the backoff drops from the end."""
    return tuple(o for j, o in enumerate(universe) if bits >> j & 1)


def se(x):
    return x.std() / math.sqrt(max(1, len(x)))


rng = np.random.default_rng(20261112)
mask_u = tuple(o for d in range(1, reach + 1) for o in (-d, d))
left_u = (-1, -2, -3, -4, -5)
skip_u = {2: (-2, -3), 3: (-3, -4)}
for name in cp.NAMES:
    train = np.concatenate(count[name])
    counts0 = np.bincount(train, minlength=VOID + 1).astype(np.float64)
    base = (counts0 + 0.5) / (counts0.sum() + 0.5 * (VOID + 1))

    # ---- the read's stretches, cut and masked by the pass's law
    rows = {"mask_whole": [], "mask_run": [], "next": [], "skip2": [], "skip3": []}
    taken = 0
    for piece, closes in held[name]:
        body = len(piece) - (NEAR if closes else 0)
        cur = 0
        while cur < body and taken < read_places:
            rest = body - cur
            oq, oa = rng.integers(OCTAVES), rng.integers(OCTAVES)
            q = (LEAST << oq) + int(rng.integers(LEAST << oq))
            a = (LEAST << oa) + int(rng.integers(LEAST << oa))
            if rest >= q + a + LEAST:
                n, ends = q + a, False
            else:
                q = min(q, rest - 1)
                n, ends = rest, closes
            s = piece[cur: cur + n + (NEAR if ends else 0)]
            cur += n
            taken += len(s)
            if q < 1 or len(s) - q < 1:
                continue
            if rng.integers(2):                      # the writer's state at k = 0: the context known, the run open
                rows["next"].append((s, q, None))
                for d in (2, 3):
                    if q + d - 1 < len(s):
                        rows["skip%d" % d].append((s, q + d - 1, None))
                continue
            u = (int(rng.integers(1 << 16)) + 1) / 65536.0
            whole = bool(rng.integers(2))
            frm = 0 if whole else q
            m = np.zeros(len(s), dtype=bool)
            m[frm:] = rng.random(len(s) - frm) < max(u * u, 1.0 / 65536)
            if not m.any():
                m[frm + int(rng.integers(len(s) - frm))] = True
            rows["mask_whole" if whole else "mask_run"].append((s, None, m))
    edge = {id(s): at for s, at, _ in rows["next"]}   # a one-place row's context ends where its stretch's does

    def gather(kind, universe):
        cls, pats, ctx = [], [], {o: [] for o in universe}
        for s, at, m in rows[kind]:
            n = len(s)
            if m is None:
                idx = np.array([at])
                known = np.zeros(n, dtype=bool)
                known[: edge[id(s)]] = True
            else:
                idx, known = np.nonzero(m)[0], ~m
            cls.append(s[idx])
            pat = np.zeros(len(idx), dtype=np.int64)
            for j, o in enumerate(universe):
                pos = idx + o
                ok = (pos >= 0) & (pos < n)
                kn = np.zeros(len(idx), dtype=bool)
                kn[ok] = known[pos[ok]]
                sy = np.zeros(len(idx), dtype=np.uint16)
                sy[ok] = s[pos[ok]]
                ctx[o].append(sy)
                pat |= kn.astype(np.int64) << j
            pats.append(pat)
        return np.concatenate(cls), {o: np.concatenate(v) for o, v in ctx.items()}, np.concatenate(pats)

    tables = {}

    def need(universe, pattern):
        chains = {}
        for pat in np.unique(pattern):
            ch = chain_of(universe, int(pat))
            chains[int(pat)] = ch
            for depth in range(1, len(ch) + 1):
                if ch[:depth] not in tables:
                    tables[ch[:depth]] = table(train, ch[:depth])
        return chains

    print("RULER slice=%s counts_octets=%d read_places=%d classes_order0=%.4f" % (name, len(train), taken, -(base * np.log(base)).sum()))
    for kind in ("mask_whole", "mask_run"):
        cls, ctx, pat = gather(kind, mask_u)
        x0 = -np.log(base[cls.astype(np.int64)])
        got = ["  %s places=%d order0=%.4f" % (kind, len(cls), x0.mean())]
        for r in range(1, reach + 1):
            pr = pat & ((1 << (2 * r)) - 1)
            x = code(tables, base, need(mask_u[: 2 * r], pr), cls, ctx, pr)
            got.append("reach%d=%.4f" % (r, x.mean()))
        got.append("se=%.4f" % se(x))
        both, none = (pat & 3) == 3, (pat & 3) == 0
        one = ~both & ~none
        far = none & ((pat & 12) == 0)
        got.append("| nearest_known both=%.3f one=%.3f neither=%.3f neither_within_2=%.3f" % (both.mean(), one.mean(), none.mean(), far.mean()))
        got.append("| reach%d by them both=%.4f one=%.4f neither=%.4f neither_within_2=%.4f" % (reach, x[both].mean(), x[one].mean(), x[none].mean(), x[far].mean()))
        got.append("| order0 by them both=%.4f one=%.4f neither=%.4f" % (x0[both].mean(), x0[one].mean(), x0[none].mean()))
        print(" ".join(got))
    cls, ctx, pat = gather("next", left_u)
    got = ["  next places=%d order0=%.4f" % (len(cls), (-np.log(base[cls.astype(np.int64)])).mean())]
    for r in range(1, 6):
        pr = pat & ((1 << r) - 1)
        x = code(tables, base, need(left_u[:r], pr), cls, ctx, pr)
        got.append("left%d=%.4f(se %.4f)" % (r, x.mean(), se(x)))
    print(" ".join(got))
    for d in (2, 3):
        cls, ctx, pat = gather("skip%d" % d, skip_u[d])
        x = code(tables, base, need(skip_u[d], pat), cls, ctx, pat)
        print("  distance%d places=%d order0=%.4f two_nearest_known=%.4f(se %.4f)" % (d, len(cls), (-np.log(base[cls.astype(np.int64)])).mean(), x.mean(), se(x)))
    print("  cells " + " ".join("left%d=%d contexts, %d pairs" % (r, len(tables[left_u[:r]][2]), len(tables[left_u[:r]][0])) for r in range(1, 6))
          + "  s=%.0f" % (time.time() - t0), flush=True)
