"""The ring's turn at the held-out units, read outside the machine (an exterior reading).

Usage: python3 -I RING_PHASE_CENTROIDS.py READ.txt [READ.txt ...] [harmonics=H,H,...]
Each READ is a `read-tower-at` read of a ring-faced tower at the cells before each held-out sum's
units digit; its FORMS lines carry, per cell, the arriving class and the ring's face (re, im per
harmonic). For each read: each units class's mean turn of the first harmonic (degrees) and its
resultant length, and a leave-one-out nearest-centroid read of the units from the first harmonic
alone and from every harmonic the face carries, each cell's harmonic parts taken at unit length.
With harmonics=H,H,... the nearest-centroid read is taken from each listed count of leading
harmonics instead (the characters a founded turn resolves at the read cells).
"""
import cmath, collections, math, sys

paths = [a for a in sys.argv[1:] if not a.startswith('harmonics=')]
listed = [int(h) for a in sys.argv[1:] if a.startswith('harmonics=') for h in a[len('harmonics='):].split(',')]
for path in paths:
    rows = [l.split() for l in open(path) if l.startswith('FORMS')]
    cells = [(int(r[2]), [complex(int(r[3 + 2 * h]), int(r[4 + 2 * h])) for h in range((len(r) - 3) // 2)]) for r in rows]
    unit = lambda z: z / abs(z) if z else 0
    cells = [(k, [unit(z) for z in zs]) for k, zs in cells]
    harmonics = len(cells[0][1])
    by = collections.defaultdict(list)
    for k, zs in cells:
        by[k].append(zs[0])
    print(path, 'cells', len(cells), 'harmonics', harmonics)
    for k in sorted(by):
        m = sum(by[k]) / len(by[k])
        print(f"  {chr(k)}: {len(by[k])} cells, mean turn {math.degrees(cmath.phase(m)) % 360:.1f} degrees, resultant {abs(m):.3f}")
    for use in sorted({h for h in listed if h <= harmonics} if listed else {1, harmonics}):
        right = 0
        sums = collections.defaultdict(lambda: [0j] * use)
        count = collections.Counter()
        for k, zs in cells:
            sums[k] = [a + b for a, b in zip(sums[k], zs[:use])]
            count[k] += 1
        for k, zs in cells:
            best, score = None, None
            for c in sums:
                n = count[c] - (c == k)
                if n == 0:
                    continue
                cent = [(s - (z if c == k else 0)) / n for s, z in zip(sums[c], zs[:use])]
                v = sum((z.conjugate() * w).real for z, w in zip(zs[:use], cent))
                if score is None or v > score:
                    best, score = c, v
            right += best == k
        print(f"  leave one out, {use} harmonic(s): {right} of {len(cells)}")
