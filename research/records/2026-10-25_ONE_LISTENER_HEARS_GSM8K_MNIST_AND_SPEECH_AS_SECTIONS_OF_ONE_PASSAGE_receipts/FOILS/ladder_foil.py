"""Exterior foil: the founded first level of a gated tower (64 modes, 8 rungs of 8, |λ| = 1 − 2^−s,
s = 1..8, input scaled by γ = √(1 − |λ|²)), on a random class encoding (width 64) and random push,
under three founded turn ladders:
- current: turn jπ/8 on every rung (the tower's founding);
- still:   no turn on any mode;
- scaled:  turn jπ/2^(s+2) on rung s, so a mode turns at most about one turn over its memory 2^s.
State at the section's end (image->label), read by nearest class mean scaled (all 128 coordinates)
and pooled covariance on the four slowest rungs (64 coordinates). Integers on 2^24; the turn faces
by exact half-angle recursion (integer square roots). Keys: a fixed linear congruential draw."""
import importlib.util, struct, sys
spec = importlib.util.spec_from_file_location('probe', sys.argv[2]); probe = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
B = 24; ONE = 1 << B
def isqrt(n): 
    import math; return math.isqrt(n)
def rel(x, b=B): return (x + (1 << (b - 1))) >> b
def ladder(n):  # e^(iπ/2^i), i = 0..n, on 2^B
    out = [(-ONE, 0), (0, ONE)]; F = 60; one = 1 << F; c, s = 0, one
    for _ in range(1, n):
        half = isqrt(((one + c) << F) >> 1); s = (s << F) // (2 * half); c = half
        out.append((c >> (F - B), s >> (F - B)))
    return out
L = ladder(14)
def face(j, n):  # e^(iπ j / 2^n)
    v = (ONE, 0)
    for i in range(n + 1):
        if j >> (n - i) & 1:
            cr, ci = L[i]; v = (rel(v[0] * cr - v[1] * ci), rel(v[0] * ci + v[1] * cr))
    return v
seed = [12345]
def draw():  # uniform in [-1, 1) on 2^B
    seed[0] = (seed[0] * 6364136223846793005 + 1442695040888963407) % (1 << 64)
    return (seed[0] >> 40) - (1 << 23) << (B - 24 + 1) >> 1
W, N = 64, 64
enc = [[draw() for _ in range(W)] for _ in range(257)]
push = [[(draw() // 8, draw() // 8) for _ in range(W)] for _ in range(N)]  # 1/√64
pushed = [[(rel(sum(push[k][i][0] * enc[c][i] for i in range(W))), rel(sum(push[k][i][1] * enc[c][i] for i in range(W)))) for k in range(N)] for c in range(257)]
def moves(kind):
    out = []
    for k in range(N):
        s, j = k // 8 + 1, k % 8
        rho = ONE - (ONE >> s)
        gamma = isqrt(ONE * ONE - rho * rho)
        if kind == 'current': u = face(j, 3)
        elif kind == 'still': u = (ONE, 0)
        else: u = face(j, s + 2)
        out.append(((rel(u[0] * rho), rel(u[1] * rho)), gamma))
    return out
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
def state(ms, classes):
    h = [(0, 0)] * N
    for c in classes:
        p = pushed[c]
        h = [(rel(x * a - y * b) + rel(g * p[k][0]), rel(x * b + y * a) + rel(g * p[k][1])) for k, ((x, y), ((a, b), g)) in enumerate(zip(h, ms))]
    return [v for xy in h for v in xy]
for kind in sys.argv[3:]:
    ms = moves(kind)
    a = [(lab, state(ms, cl)) for lab, cl in sections(sys.argv[1], 'train')]
    b = [(lab, state(ms, cl)) for lab, cl in sections(sys.argv[1], 'dev')]
    w = 2 * N; model = probe.fit(a, w); kept, sc = probe.scatter(a, model, w)
    near = sum(probe.nearest_scaled(model, kept, sc, x) == c for c, x in b)
    slow = list(range(64, 128))
    a2 = [(c, [x[i] for i in slow]) for c, x in a]; b2 = [(c, [x[i] for i in slow]) for c, x in b]
    lda = probe.pooled(a2, probe.fit(a2, 64), 64)
    pooled = 'singular' if lda is None else sum(probe.discriminant(lda, x) == c for c, x in b2)
    print(f"{kind}: nearest_mean_scaled {near} pooled_slow4 {pooled} of {len(b)}", flush=True)
