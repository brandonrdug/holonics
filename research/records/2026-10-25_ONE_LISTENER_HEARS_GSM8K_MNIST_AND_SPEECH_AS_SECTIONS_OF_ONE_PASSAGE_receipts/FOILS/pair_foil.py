"""Exterior foil: one rung (s = 5) of moments of the 9 turn classes, read four ways:
- zero_turn: the non-rotating moments (9);
- rotated:   the moments rotating by (4+3i)/5 a class, as the state holds them at the end (18);
- energies:  their squared moduli (9);
- pairs:     Re and Im of h_a conj(h_b), a <= b, same rotation (90): shift-invariant pair reads.
Fixed point on 2^20, released to the nearest; products released by 2^20. Nearest class mean scaled."""
import importlib.util, struct, sys
spec = importlib.util.spec_from_file_location('probe', sys.argv[2]); probe = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
S, ONE, (RE, IM, D) = 5, 1 << 20, (4, 3, 5)
def rnd(a, b):
    return (2 * a + b) // (2 * b)
def sections(prefix, side):
    raw = open(f"{prefix}.{side}.classes", 'rb').read(); cl = struct.unpack(f">{len(raw)//2}H", raw)
    mk = open(f"{prefix}.{side}.marks", 'rb').read(); i = 0
    while i < len(cl):
        if mk[i] != 5:
            i += 1; continue
        j = i
        while j < len(cl) and mk[j] == 5:
            j += 1
        if j + 1 < len(cl) and mk[j] == 7 and mk[j + 1] == 1:
            yield cl[j + 1], cl[i:j]
        i = j
def feats(octets):
    z = [0] * 9; h = [[0, 0] for _ in range(9)]
    k = 0
    while k < len(octets):
        o = octets[k]; k += 1
        t = o >> 4
        if t == 8:
            k += 2
        for q in range(9):
            z[q] -= z[q] >> S
            x, y = h[q]; x, y = rnd(x * RE - y * IM, D), rnd(x * IM + y * RE, D)
            h[q] = [x - (x >> S), y - (y >> S)]
        z[t] += ONE; h[t][0] += ONE
    rot = [c for p in h for c in p]
    en = [(x * x + y * y) >> 20 for x, y in h]
    pairs = []
    for a in range(9):
        for b in range(a, 9):
            (xa, ya), (xb, yb) = h[a], h[b]
            pairs += [(xa * xb + ya * yb) >> 20, (ya * xb - xa * yb) >> 20]
    return z, rot, en, pairs
names = ('zero_turn', 'rotated', 'energies', 'pairs')
def cells(side):
    out = tuple([] for _ in names)
    for label, octets in sections(sys.argv[1], side):
        for f, m in zip(out, feats(octets)):
            f.append((label, m))
    return out
train, held = cells('train'), cells('dev')
for name, a, b in zip(names, train, held):
    w = len(a[0][1]); model = probe.fit(a, w); kept, sc = probe.scatter(a, model, w)
    line = f"{name} ({len(kept)} varying of {w}): nearest_mean_scaled {sum(probe.nearest_scaled(model, kept, sc, x) == c for c, x in b)}"
    if len(kept) <= 96:
        a2 = [(c, [x[i] for i in kept]) for c, x in a]; b2 = [(c, [x[i] for i in kept]) for c, x in b]
        lda = probe.pooled(a2, probe.fit(a2, len(kept)), len(kept))
        line += f" pooled_covariance {'singular' if lda is None else sum(probe.discriminant(lda, x) == c for c, x in b2)}"
    print(line, 'of', len(b), flush=True)
