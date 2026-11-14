"""redraw_ruler: read-redraw's rows (G169) as nats a place, pooled over the slices and by slice (a host ruler; numbers only).

usage: python3 -I redraw_ruler.py OUT_DIR (read-redraw's or read-breakdown's; the latter adds the opened written places' code before each
section's step, `evidence`, and the sections that deposited)
Codes on 2^-20 bits are read as nats (code / 2^20 ln 2). `pair_ratio` is the neighbouring open places that changed together over the
independent count at the sweep's rate of change ((pair_flips / pairs) / (flips / places)^2).
"""
import math
import sys

LN2 = math.log(2.0)
SLICES = ["code", "web", "science", "books", "wikidata"]


def nats(code, places):
    return code / float(1 << 20) * LN2 / max(places, 1)


rows = [line.rstrip("\n").split("\t") for line in open(sys.argv[1] + "/redraw.tsv")][1:]
by = {}
for r in rows:
    s, w = int(r[0]), int(r[1])
    by.setdefault(w, {})[s] = [int(x) for x in r[2:]]
for w in sorted(by):
    width = len(next(iter(by[w].values())))
    tot = [sum(v[i] for v in by[w].values()) for i in range(width)]
    places, code, expected, agree, flips, pair_flips, pairs, snaps, snap_places, average, own, against = tot[:12]
    evidence = f" evidence={nats(tot[13], tot[12]):.4f}({tot[12]}) deposited={tot[14]}" if width >= 15 else ""
    rate = flips / max(places, 1)
    ratio = (pair_flips / max(pairs, 1)) / rate ** 2 if rate > 0 else 0.0
    slices = " ".join(f"{SLICES[s]}={nats(v[1], v[0]):.4f}/{nats(v[9], v[0]):.4f}" for s, v in sorted(by[w].items()))
    print(f"sweep={w} places={places} code={nats(code, places):.4f} expected={nats(expected, places):.4f} average={nats(average, places):.4f}"
          f" own={nats(own, places):.4f} agree={agree / places:.4f} flips={rate:.4f} pair_ratio={ratio:.3f} snaps={snaps}/{snap_places}"
          f" confident_against={against / places:.4f}{evidence} | code/average {slices}")
