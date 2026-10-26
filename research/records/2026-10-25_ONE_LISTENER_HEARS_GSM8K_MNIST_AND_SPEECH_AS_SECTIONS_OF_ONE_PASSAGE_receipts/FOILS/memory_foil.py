"""Exterior foils: what fading moments of the stroke chart carry of the digit (integers only).

For each image->label section, three moment families over the image's classes, each kept at the
rungs s = 2..7 (decay 1 - 2^-s a class, dyadic: m <- m - (m >> s) + 2^20 [event]):
- turns:    the classes' turn values (0..8, 8 a jump) and octaves, as they arrive (what a fading
            linear sum of the classes can hold, the gated tower's kind of memory);
- heading:  the accumulated heading (the turns summed mod 8, reset at a jump): a phase;
- place:    the pen's place (row, column) and its squares and product, the heading accumulated again.
Probed by probe.py's nearest class mean scaled by within-label scatter, and pooled covariance.
"""
import importlib.util, struct, sys
spec = importlib.util.spec_from_file_location('probe', sys.argv[2]); probe = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
DIRS = ((0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1))
RUNGS = range(2, 8)

def sections(prefix, side):
    raw = open(f"{prefix}.{side}.classes", 'rb').read()
    cl = struct.unpack(f">{len(raw)//2}H", raw)
    mk = open(f"{prefix}.{side}.marks", 'rb').read()
    i = 0
    while i < len(cl):
        if mk[i] != 5:
            i += 1; continue
        j = i
        while j < len(cl) and mk[j] == 5:
            j += 1
        if j + 1 < len(cl) and mk[j] == 7 and mk[j + 1] == 1:
            yield cl[j + 1], cl[i:j]
        i = j

def moments(octets):
    turns = {s: [0] * 17 for s in RUNGS}
    head = {s: [0] * 8 for s in RUNGS}
    place = {s: [0] * 5 for s in RUNGS}
    heading, r, c = 0, 0, 0
    k = 0
    while k < len(octets):
        o = octets[k]; k += 1
        t, octave = o >> 4, o & 15
        if t == 8:
            dr, dc = struct.unpack('bb', bytes(octets[k:k + 2])); k += 2
            r, c, heading = r + dr, c + dc, 0
        else:
            heading = (heading + t) % 8
            r, c = r + DIRS[heading][0], c + DIRS[heading][1]
        for s in RUNGS:
            for v in (turns[s], head[s], place[s]):
                for q in range(len(v)):
                    v[q] -= v[q] >> s
            turns[s][t] += 1 << 20
            turns[s][9 + min(octave, 7)] += 1 << 20
            head[s][heading] += 1 << 20
            for q, x in enumerate((r, c, r * r, c * c, r * c)):
                place[s][q] += x << 20
    flat = lambda d: [x for s in RUNGS for x in d[s]]
    return flat(turns), flat(head), flat(place)

def cells(prefix, side):
    out = ([], [], [])
    for label, octets in sections(prefix, side):
        for f, m in zip(out, moments(octets)):
            f.append((label, m))
    return out

train, held = cells(sys.argv[1], 'train'), cells(sys.argv[1], 'dev')
for name, a, b in zip(('turns', 'heading', 'place'), train, held):
    w = len(a[0][1])
    print(f"== {name} ({w} coordinates)")
    model = probe.fit(a, w)
    kept, sc = probe.scatter(a, model, w)
    print('nearest_mean_scaled held_out', sum(probe.nearest_scaled(model, kept, sc, x) == c for c, x in b), 'of', len(b))
    a2 = [(c, [x[k] for k in kept]) for c, x in a]; b2 = [(c, [x[k] for k in kept]) for c, x in b]
    m2 = probe.fit(a2, len(kept))
    lda = probe.pooled(a2, m2, len(kept))
    print('pooled_covariance held_out', 'singular' if lda is None else sum(probe.discriminant(lda, x) == c for c, x in b2), 'coordinates', len(kept))
