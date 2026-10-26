"""Exterior foil: rotating fading moments of the stroke classes, read at the section's end (the
recurrent state) or in the section's own clock (the phase anchored at the section's first class).

Input per class: one-hot of its turn (0..8) and octave (0..7), 17 features. Modes: rungs s in
{3, 5, 7} (decay 1 - 2^-s) times rotations: none, and the rational unit turns (4+3i)/5, (12+5i)/13,
(24+7i)/25 (about 37, 23 and 16 degrees a class). Fixed point on 2^20, released to the nearest.
- real:     the non-rotating moments (17 x 3);
- at_end:   the rotating moments as the state holds them at the end (rot^(n-1-k));
- own_clock: the same decays, the phase anchored at the section's start (rot^(-k)).
"""
import importlib.util, struct, sys
spec = importlib.util.spec_from_file_location('probe', sys.argv[2]); probe = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
RUNGS = (3, 5, 7)
ROTS = ((4, 3, 5), (12, 5, 13), (24, 7, 25))
ONE = 1 << 20

def rnd(a, b):
    return (2 * a + b) // (2 * b) if b > 0 else -rnd(-a, -b)

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

def features(octets):
    real = [[0] * 17 for _ in RUNGS]
    end = [[[0, 0] for _ in range(17)] for _ in RUNGS for _ in ROTS]
    own = [[[0, 0] for _ in range(17)] for _ in RUNGS for _ in ROTS]
    phase = [[ONE, 0] for _ in ROTS]  # rot^(-k), released
    for o in octets:
        t, octave = o >> 4, o & 15
        idx = (t, 9 + min(octave, 7))
        for a, s in enumerate(RUNGS):
            v = real[a]
            for q in range(17):
                v[q] -= v[q] >> s
            for q in idx:
                v[q] += ONE
            for b, (re, im, d) in enumerate(ROTS):
                e, w = end[a * len(ROTS) + b], own[a * len(ROTS) + b]
                for q in range(17):
                    x, y = e[q]
                    x, y = rnd(x * re - y * im, d), rnd(x * im + y * re, d)
                    e[q] = [x - (x >> s), y - (y >> s)]
                    x, y = w[q]
                    w[q] = [x - (x >> s), y - (y >> s)]
                for q in idx:
                    e[q][0] += ONE
                    w[q][0] += phase[b][0]; w[q][1] += phase[b][1]
        for b, (re, im, d) in enumerate(ROTS):
            x, y = phase[b]
            phase[b] = [rnd(x * re + y * im, d), rnd(-x * im + y * re, d)]  # times conj(rot)
    flat = lambda m: [c for row in m for pair in row for c in pair]
    return [x for row in real for x in row], flat(end), flat(own)

def cells(prefix, side):
    out = ([], [], [])
    for label, octets in sections(prefix, side):
        for f, m in zip(out, features(octets)):
            f.append((label, m))
    return out

train, held = cells(sys.argv[1], 'train'), cells(sys.argv[1], 'dev')
for name, a, b in zip(('real', 'at_end', 'own_clock'), train, held):
    w = len(a[0][1])
    model = probe.fit(a, w)
    kept, sc = probe.scatter(a, model, w)
    print(f"{name} ({w} coordinates, {len(kept)} varying): nearest_mean_scaled held_out", sum(probe.nearest_scaled(model, kept, sc, x) == c for c, x in b), 'of', len(b), flush=True)
