"""Per rank of a ring-faced tower: each class's mean first-harmonic turn at the read cells and a
leave-one-out nearest-centroid read from that rank's harmonics (an exterior reading).
Usage: python3 -I RING_RANK_CENTROIDS.py READ.txt RANKS HARMONICS"""
import cmath, collections, math, sys
path, ranks, hs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rows = [l.split() for l in open(path) if l.startswith('FORMS')]
unit = lambda z: z / abs(z) if z else 0
for r in range(ranks):
    cells = []
    for row in rows:
        v = [int(x) for x in row[3:]]
        zs = [unit(complex(v[2 * (r * hs + h)], v[2 * (r * hs + h) + 1])) for h in range(hs)]
        cells.append((chr(int(row[2])), zs))
    by = collections.defaultdict(list)
    for k, zs in cells: by[k].append(zs)
    line = []
    for k in sorted(by):
        m = sum(z[0] for z in by[k]) / len(by[k])
        line.append(f"{k}:{len(by[k])}@{math.degrees(cmath.phase(m)) % 360:.0f}/{abs(m):.2f}")
    res = []
    for use in range(1, hs + 1):
        sums = {k: [sum(z[h] for z in by[k]) for h in range(use)] for k in by}
        right = 0
        for k, zs in cells:
            best = max((c for c in by if len(by[c]) - (c == k) > 0), key=lambda c: sum(((sums[c][h] - (zs[h] if c == k else 0)) / (len(by[c]) - (c == k)) * zs[h].conjugate()).real for h in range(use)))
            right += best == k
        res.append(f"{use}h:{right}")
    print(f"rank {r}: {' '.join(line)}\n  leave one out of {len(cells)}: {' '.join(res)}")
