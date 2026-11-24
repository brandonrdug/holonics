#!/usr/bin/env python3
"""Which register a write lands in (the lead, November 24; Brandon's 16:18Z reading of her probe writes: does a name pull her into the
part of her passage where it lives?).

    python3 tools/register_ruler.py STORE FORMS [FORMS ...] [--group LABEL_FIELD] [--octets N]

A ruler on the host, outside the machine: for every slice of STORE it counts the byte trigrams of the first N octets of the slice's
training documents (`DOCS_<slice>.bin`, default 24 MB), and it reads each write as the slice under whose counts its trigrams cost the
fewest bits (add-one over the trigrams the slice holds; a write's cost is the sum over its own trigrams). It changes nothing it reads.

Before any write is read, the ruler is held to a planted law (rule 11): 400 windows of 64 octets cut from each slice's held documents
(`HELD_<slice>.bin`, which no count was taken from) are read the same way, and the share it places in their own slice is printed per
slice, with the share it places in `ours`. A write of 64 places is read at the same length.

FORMS are `write-next` outputs (label, prompt, write). Writes are grouped by the label's field LABEL_FIELD (split on `:`, default 1),
and for each group the ruler prints its count of writes and the share it places in each slice, with the slices the repository and its
sessions wrote (theory, logic, dialogue, acts, harness) summed as `ours`.
"""
import math
import os
import random
import sys
from collections import Counter, defaultdict

OURS = ("theory", "logic", "dialogue", "acts", "harness")


def slices(store):
    return sorted(f[5:-4] for f in os.listdir(store) if f.startswith("DOCS_") and f.endswith(".bin"))


def counts(path, octets):
    with open(path, "rb") as f:
        b = f.read(octets)
    c = Counter(b[i:i + 3] for i in range(len(b) - 2))
    return c, sum(c.values())


class Ruler:
    def __init__(self, store, octets):
        self.names = slices(store)
        self.tables = {s: counts(os.path.join(store, f"DOCS_{s}.bin"), octets) for s in self.names}
        self.vocab = len(set().union(*(set(c) for c, _ in self.tables.values()))) + 1

    def cost(self, s, text):
        c, n = self.tables[s]
        return -sum(math.log2((c.get(text[i:i + 3], 0) + 1) / (n + self.vocab)) for i in range(len(text) - 2))

    def place(self, text):
        return min(self.names, key=lambda s: self.cost(s, text))


def planted(ruler, store, per=400, width=64, seed=24):
    rng = random.Random(seed)
    out = {}
    for s in ruler.names:
        p = os.path.join(store, f"HELD_{s}.bin")
        if not os.path.exists(p):
            continue
        b = open(p, "rb").read()
        if len(b) < width * 2:
            continue
        placed = [ruler.place(b[o:o + width]) for o in (rng.randrange(0, len(b) - width) for _ in range(per))]
        out[s] = (sum(x == s for x in placed) / per, sum(x in OURS for x in placed) / per)
    return out


def main(argv):
    group, octets, args = 1, 24_000_000, []
    i = 0
    while i < len(argv):
        if argv[i] == "--group":
            group = int(argv[i + 1]); i += 2
        elif argv[i] == "--octets":
            octets = int(argv[i + 1]); i += 2
        else:
            args.append(argv[i]); i += 1
    if len(args) < 2:
        sys.exit(__doc__)
    store, forms = args[0], args[1:]
    ruler = Ruler(store, octets)
    p = planted(ruler, store)
    print("REGISTER_PLANTED", " ".join(f"{s} {v[0]:.2f}" for s, v in p.items()),
          f"| mean {sum(v[0] for v in p.values()) / max(len(p), 1):.2f} of 64-octet held windows placed in their own slice")
    print("REGISTER_PLANTED_OURS", " ".join(f"{s} {v[1]:.2f}" for s, v in p.items()),
          "| the share of each slice's held windows placed in ours (theory, logic, dialogue, acts, harness)")
    for f in forms:
        groups = defaultdict(Counter)
        for line in open(f, encoding="utf-8", errors="replace"):
            r = line.rstrip("\n").split("\t")
            if len(r) < 3:
                continue
            key = r[0].split(":")[group] if len(r[0].split(":")) > group else r[0]
            w = r[2].replace("\\n", "\n").replace("\\t", "\t").encode("utf-8", errors="replace")
            groups[key][ruler.place(w)] += 1
        lab = f.rstrip("/").split("/")[-2] if "/" in f else f
        for key, c in groups.items():
            n = sum(c.values())
            ours = sum(c[s] for s in OURS)
            print(f"REGISTER {lab} {key} n={n} ours={ours / n:.2f} |",
                  " ".join(f"{s} {c[s] / n:.2f}" for s in ruler.names if c[s]))


if __name__ == "__main__":
    main(sys.argv[1:])
