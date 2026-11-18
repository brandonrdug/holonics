#!/usr/bin/env -S python3 -I
"""A ruler: how far a row for each of the K places before a place can close what those places settle, against a count that binds
them (the lead, November 18; the record of the two streams §17).

A row of the opening for the j-th place before a place (`tower.region-second` and the rows that would follow it) adds that place's
symbol to the place's state by itself. The most a face can make of K such rows with nothing binding them is the additive reader
fitted here: a face whose logarithm is a sum of one row a place, `log p(y | u_1 .. u_K) = b(y) + Σ_j W_j[u_j, y] − log Z`, fitted by
descent of its code on the first TRAIN octets of a slice's training documents (it opens on the count of one place and the rows of
the farther places at zero). A count of the same K places binds them as one context. So the pair is a ladder for a part: what K
rows can reach alone, and what is left to a conjunction.

Read on the frontier places of a `read-cavity` output (the same places and the same bins as `frontier_excess_ruler.py`: a place's
bin is the news the count of KMAX places expects there, a property of what stands before the place), for every K from 1 to KMAX:
the additive reader's code and the mean mass it gives the arriving symbol (`draw_agrees`), beside the count's at the same K and
each named read's rows of KIND. With LEXICON and PANEL the additive reader also writes from the panel's prompts as
`count_writer_ruler.py`'s count does, and the share of its written words standing in the slice's lexicon is printed.

The fit prints its held code after every pass over the fitted text, so a reader sees where it stopped falling. A host instrument,
in floats: a fitted table enters no law, and the additive reader is no part of the machine. Codes, masses and counts only.

Usage: additive_rows_ruler.py STORE CODEC SLICE TRAIN_OCTETS KMAX PASSES KIND NAME=DIR [NAME=DIR ...] [-- LEXICON PANEL PLACES DRAWS]"""
import math, os, pickle, random, re, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_excess_ruler import fit, news, G, LN2, EDGES, NAMES

NONE = 256            # a place before the passage's first
BATCH = 16384
WORD = re.compile(r"[A-Za-z]{2,}")

def contexts(seq, at, k):
    """The symbols at 1..k places before each place of `at` (NONE before the passage's first)."""
    cols = []
    for j in range(1, k + 1):
        src = at - j
        cols.append(np.where(src >= 0, seq[np.maximum(src, 0)], NONE))
    return np.stack(cols, axis=1)

def logits_of(w, b, ctx):
    out = np.broadcast_to(b, (ctx.shape[0], 256)).copy()
    for j in range(ctx.shape[1]):
        out += w[j][ctx[:, j]]
    return out

def softmax(z):
    z = z - z.max(axis=1, keepdims=True)
    np.exp(z, out=z)
    z /= z.sum(axis=1, keepdims=True)
    return z

def fit_additive(train, k, passes, held_ctx, held_y, rng):
    """Descent of the code (Adam; a pass is the fitted text once, in a drawn order, the step halved each pass)."""
    seq = np.frombuffer(train, dtype=np.uint8).astype(np.int64)
    n = len(seq)
    # Opening: the count of one place in the first row, the farther rows at zero.
    pair = np.ones((257, 256))
    np.add.at(pair, (seq[:-1], seq[1:]), 1.0)
    w = np.zeros((k, 257, 256), dtype=np.float32)
    w[0] = np.log(pair / pair.sum(axis=1, keepdims=True)).astype(np.float32)
    b = np.zeros(256, dtype=np.float32)
    m_w, v_w, m_b, v_b = np.zeros_like(w), np.zeros_like(w), np.zeros_like(b), np.zeros_like(b)
    step, t, trace = 0.02, 0, []
    for p in range(passes):
        order = rng.permutation(np.arange(k, n))
        for s in range(0, len(order), BATCH):
            at = order[s:s + BATCH]
            ctx, y = contexts(seq, at, k), seq[at]
            g = softmax(logits_of(w, b, ctx))
            g[np.arange(len(at)), y] -= 1.0
            g /= len(at)
            g_w = np.zeros_like(w)
            for j in range(k):
                o = np.argsort(ctx[:, j], kind="stable")
                keys = ctx[o, j]
                starts = np.flatnonzero(np.r_[True, keys[1:] != keys[:-1]])
                g_w[j][keys[starts]] = np.add.reduceat(g[o], starts, axis=0)
            g_b = g.sum(axis=0)
            t += 1
            for par, grad, m, v in ((w, g_w, m_w, v_w), (b, g_b, m_b, v_b)):
                m *= 0.9; m += 0.1 * grad
                v *= 0.999; v += 0.001 * grad * grad
                par -= step * (m / (1 - 0.9 ** t)) / (np.sqrt(v / (1 - 0.999 ** t)) + 1e-8)
        step /= 2
        trace.append(float(-np.log(softmax(logits_of(w, b, held_ctx))[np.arange(len(held_y)), held_y]).mean()))
    return w, b, trace

def main():
    args = sys.argv[1:]
    tail = []
    if "--" in args:
        tail = args[args.index("--") + 1:]
        args = args[:args.index("--")]
    store, codec, name = args[0], args[1], args[2]
    train_n, kmax, passes, kind = int(args[3]), int(args[4]), int(args[5]), args[6]
    reads = [a.split("=", 1) for a in args[7:]]
    head, used = open(codec).read().split("\n")[:2]
    void = int(head.split(" ")[2])
    used = [int(w) for w in used.split(" ")]
    octet = lambda c: None if c == void else (used[c] if c < void else used[c - 1])
    places = {}
    for line in open(reads[0][1] + "/cavity.tsv"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "P" and f[1] == name:
            places.setdefault(int(f[2]), {})[int(f[3])] = int(f[4])
    codes = []
    for _, d in reads:
        rows = {}
        for line in open(d + "/frontier.tsv"):
            f = line.rstrip("\n").split("\t")
            if f[0] == kind and f[1] == name:
                rows[(int(f[2]), int(f[3]))] = int(f[5]) / G * LN2
        codes.append(rows)
    train = open(f"{store}/DOCS_{name}.bin", "rb").read(train_n)
    model = fit(train, kmax)
    # The held places: their symbol, their K places before, the count's code at every K and the news it expects at KMAX.
    held_ctx, held_y, held_bin, count_code, read_code = [], [], [], [], []
    for stretch, st in sorted(places.items()):
        n = max(st) + 1
        seq = [octet(st.get(t, void)) for t in range(n)]
        raw = bytes(255 if x is None else x for x in seq)
        for t in range(1, n):
            key = (stretch, t)
            if seq[t] is None or any(key not in rows for rows in codes):
                continue
            by_k, expected = news(model, raw, t, kmax)
            held_ctx.append([raw[t - j] if t - j >= 0 else NONE for j in range(1, kmax + 1)])
            held_y.append(raw[t])
            held_bin.append(sum(1 for e in EDGES if expected >= e))
            count_code.append(by_k)
            read_code.append([rows[key] for rows in codes])
    held_ctx, held_y, held_bin = np.array(held_ctx), np.array(held_y), np.array(held_bin)
    count_code, read_code = np.array(count_code), np.array(read_code)
    count = len(held_y)
    sets = [(nm, held_bin == i) for i, nm in enumerate(NAMES)] + [("all", np.ones(count, dtype=bool))]
    print(f"ADDITIVE slice={name} kind={kind} places={count} train_octets={len(train)} kmax={kmax} passes={passes} shares: "
          + " ".join(f"{nm!r}={sel.mean():.3f}" for nm, sel in sets[:-1]), flush=True)
    for r, (nm, _) in enumerate(reads):
        print(f"ADDITIVE slice={name} read={nm}: " + " | ".join(
            f"{sn!r} code={read_code[sel, r].mean():.3f} draw_agrees={np.exp(-read_code[sel, r]).mean():.3f}" for sn, sel in sets if sel.any()), flush=True)
    rng = np.random.default_rng(20261118)
    fitted = {}
    for k in range(1, kmax + 1):
        w, b, trace = fit_additive(train, k, passes, held_ctx[:, :k], held_y, rng)
        fitted[k] = (w, b)
        code = -np.log(softmax(logits_of(w, b, held_ctx[:, :k]))[np.arange(count), held_y])
        print(f"ADDITIVE slice={name} places_before={k} the fit's held code after each pass: " + " ".join(f"{c:.4f}" for c in trace), flush=True)
        for label, c in ((f"rows_of_{k}_places", code), (f"count_of_{k}_places", count_code[:, k])):
            print(f"ADDITIVE slice={name} {label}: " + " | ".join(
                f"{sn!r} code={c[sel].mean():.3f} draw_agrees={np.exp(-c[sel]).mean():.3f}" for sn, sel in sets if sel.any()), flush=True)
    if tail:
        lexp, panel, n_places, draws = tail[0], tail[1], int(tail[2]), int(tail[3])
        lexicon = pickle.load(open(lexp, "rb"))[name]
        prompts = [l.rstrip("\n").split("\t")[1].replace("\\n", "\n").encode("utf-8", "replace")
                   for l in open(panel, newline="\n", errors="replace") if l.split(":")[0] == name]
        for k in range(1, kmax + 1):
            w, b = fitted[k]
            words = hits = 0
            for p, prompt in enumerate(prompts):
                for d in range(draws):
                    rnd = random.Random(f"{name}:{p}:{d}:{k}:rows")
                    seq = list(prompt[-kmax:])
                    start = len(seq)
                    for _ in range(n_places):
                        ctx = np.array([[seq[-j] if j <= len(seq) else NONE for j in range(1, k + 1)]])
                        face = softmax(logits_of(w, b, ctx))[0]
                        seq.append(rnd.choices(range(256), weights=face.tolist())[0])
                    for m in WORD.finditer(bytes(seq[start:]).decode("utf-8", "replace")):
                        words += 1
                        hits += m.group(0).lower() in lexicon
            print(f"ADDITIVE_WRITER slice={name} prompts={len(prompts)} draws={draws} places={n_places} rows_of_{k}_places: {hits}/{words}({100 * hits // max(words, 1)}%)", flush=True)

if __name__ == "__main__":
    main()
