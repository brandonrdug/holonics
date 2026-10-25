"""The echo: exact checks for sound, music, light and plasma read as round trips.

A. The round trip reads only the two bodies' relative rapidity in the medium. Sound of speed c in a
   uniform medium, an emitter-receiver of velocity a and a wall of velocity b beyond it (both relative to
   the medium, along the line): the echo is f (c - b)(c + a)/((c - a)(c + b)) = D(a/c)/D(b/c), where
   D(beta) = (1 + beta)/(1 - beta) is light's Doppler factor squared. D(x)/D(y) = D((x - y)/(1 - xy)),
   Einstein's subtraction at the speed c, so the acoustic echo is the light echo 1/k^2 with
   k^2 = D(b/c)/D(a/c). Bodies at rest relative to each other return the frequency unchanged whatever the
   wind. Two configurations with one echo can have different one-way readings: the one-way reading sees
   the medium, the round trip does not.
B. A resonator's modes are the branches of the log of its round-trip ratio rho. A loop of N cells with
   x[t + N] = rho x[t], rho a fourth root of unity in Z/p (p = 998244353, 469762049, 167772161), has its
   discrete spectrum over 4N points exactly on the bins m = r (mod 4), rho = i^r: all harmonics for
   rho = 1 (string with two fixed ends, flute with two open ends), only the odd half-harmonics for
   rho = -1 (clarinet, stopped pipe: one hard and one open end; two smooth turning points), and the
   quarter classes for rho = +-i (one hard end and one smooth turning point). Which bins inside the class
   sound depends on the excitation (part C); the class itself is the round trip's.
C. Where the pluck sits decides which harmonics sound (Young): a string of N cells with fixed ends plucked
   at cell a, odd extension over 2N points: harmonic n (0 < n < N) vanishes exactly when N | n a.
D. A plasma below its cutoff is a reactive wall: n^2 = 1 - (wp/w)^2 < 0, n = i kappa, and
   Gamma = (1 - n)/(1 + n) has |Gamma| = 1 (everything returns, late); above cutoff it is partial,
   Gamma^2 + T = 1, T = 4n/(1 + n)^2. Above cutoff w^2 = wp^2 + (ck)^2 is a mass shell (Anderson): the
   frame moving at the group velocity c^2 k/w sees the wave as a pure oscillation at wp, and
   phase times group velocity is c^2. The LC ladder with a shunt inductor (the electrons' inertia) has
   w^2 = wp^2 + 2 w0^2 (1 - cos k): a gap below wp, where cos k > 1 and the wave is evanescent.
E. The sum of all round trips. A resonator whose round trip returns rho = g u (|u| = 1, 0 < g < 1) answers
   a steady drive with H = 1/(1 - rho), the sum of rho^j; after m trips the remainder is -rho^m H and the
   energy of the m-th return is g^(2m). Re((1 + rho)/(1 - rho)) = (1 - g^2)/|1 - rho|^2 (Poisson, Airy)
   is a Doppler factor over frequency: k = (1 + g)/(1 - g) at resonance (u = 1), 1/k at antiresonance
   (u = -1), and |1 - rho|^2 = (1 - g)^2 + 4 g s, s the squared sine of half the round trip's phase. A
   Fabry-Perot cavity's transmission (1 - g)^2/|1 - rho|^2 (Airy) is that kernel divided by k.
F. The delay reads the medium. In a wind u < c a round trip of length L along the wind takes
   2Lc/(c^2 - u^2) and across it 2L/w, w^2 = c^2 - u^2: their ratio c/w exceeds 1, while the frequency
   of the return off a wall at rest is unchanged (part A, a = b).
"""
import sys
import time
from fractions import Fraction as F
from math import isqrt

T0 = time.monotonic()
PRIMES = [(998244353, 3), (469762049, 3), (167772161, 3)]


def say(part, value):
    print(part, f"elapsed_ms={int(1000 * (time.monotonic() - T0))}", value, flush=True)


def D(beta):
    return (1 + beta) / (1 - beta)


def part_a():
    ok, rows = True, []
    cases = ((F(343), F(0), F(10)), (F(343), F(-10), F(0)), (F(5), F(-3), F(-2)), (F(5), F(0), F(25, 19)),
             (F(1), F(0), F(1, 3)), (F(5), F(-3), F(-3)), (F(343), F(20), F(-49)))
    echoes, one_ways = {}, {}
    for c, a, b in cases:
        at_wall = (c - b) / (c - a)  # the wall hears the emitter on the wave moving toward +x
        echo = at_wall * (c + a) / (c + b)  # the emitter hears the wall on the wave moving toward -x
        x, y = a / c, b / c
        k2 = D(y) / D(x)
        if echo != D(x) / D(y) or echo * k2 != 1 or k2 != D((y - x) / (1 - x * y)):
            ok = False
        if a == b and echo != 1:
            ok = False
        echoes[(c, a, b)], one_ways[(c, a, b)] = echo, at_wall
        rows.append((f"c={c} a={a} b={b}", str(echo), str(at_wall)))
    # one echo, two one-way readings: the wall receding at 1 in a wind of 3, and still air at 25/19
    p, q = (F(5), F(-3), F(-2)), (F(5), F(0), F(25, 19))
    if echoes[p] != echoes[q] or one_ways[p] == one_ways[q]:
        ok = False
    # the wall receding vs the emitter receding at the same speed in still air: one echo
    if echoes[(F(343), F(0), F(10))] != echoes[(F(343), F(-10), F(0))]:
        ok = False
    return ok, rows


def ntt(x, p, g):
    n = len(x)
    w = pow(g, (p - 1) // n, p)
    return [sum(x[t] * pow(w, m * t, p) for t in range(n)) % p for m in range(n)]


def part_b():
    out, ok = {}, True
    pluck = [((7 * t * t + 3 * t + 1) % 23) - 11 for t in range(32)]
    for N in (7, 8, 17):
        for p, g in PRIMES:
            if (p - 1) % (4 * N):
                continue
            i4 = pow(g, (p - 1) // 4, p)  # a primitive fourth root of unity: the quarter turn
            for r, name in ((0, "rho=1"), (2, "rho=-1"), (1, "rho=i"), (3, "rho=-i")):
                rho = pow(i4, r, p)
                x = []
                for j in range(4):
                    x += [pluck[t] * pow(rho, j, p) % p for t in range(N)]
                w = pow(g, (p - 1) // (4 * N), p)
                # X[m] = S(m) * sum_j (rho w^(m N))^j is nonzero only where w^(m N) = rho^-1:
                # m = -r (mod 4) when w^N = i4, and m = r (mod 4) when w^N = i4^-1
                cls = (-r) % 4 if pow(w, N, p) == i4 else r
                X = ntt(x, p, g)
                outside = all(X[m] == 0 for m in range(4 * N) if m % 4 != cls)
                inside = sum(1 for m in range(4 * N) if m % 4 == cls and X[m] != 0)
                key = f"N={N} p={p} {name}"
                out[key] = {"class m mod 4": cls, "outside zero": outside, "inside nonzero": f"{inside}/{N}"}
                if not outside or inside == 0:  # which bins inside the class sound depends on the pluck (part C)
                    ok = False
    return ok, out


def part_c():
    ok, rows = True, []
    N = 16
    for a in (8, 4, 5, 3):
        shape = [t * (N - a) if t <= a else a * (N - t) for t in range(N + 1)]
        y = shape[:N] + [0] + [-shape[N - t] for t in range(1, N)]  # odd extension over 2N points
        y = y[:2 * N]
        zeros = {}
        for p, g in PRIMES:
            Y = ntt([v % p for v in y], p, g)
            zeros[p] = sorted(n for n in range(1, N) if Y[n] == 0)
        predicted = sorted(n for n in range(1, N) if (n * a) % N == 0)
        same = all(z == predicted for z in zeros.values())
        rows.append((a, predicted, same))
        if not same:
            ok = False
    return ok, rows


def cmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def cdiv(x, y):
    n = y[0] * y[0] + y[1] * y[1]
    return ((x[0] * y[0] + x[1] * y[1]) / n, (x[1] * y[0] - x[0] * y[1]) / n)


def is_square(q):
    return q >= 0 and isqrt(q.numerator) ** 2 == q.numerator and isqrt(q.denominator) ** 2 == q.denominator


def part_d():
    ok, below = True, []
    for wp_over_w, kappa in ((F(5, 4), F(3, 4)), (F(13, 12), F(5, 12)), (F(17, 8), F(15, 8))):
        if 1 - wp_over_w ** 2 != -kappa ** 2:
            ok = False
        gamma = cdiv((F(1), -kappa), (F(1), kappa))  # (1 - n)/(1 + n), n = i kappa
        if gamma[0] ** 2 + gamma[1] ** 2 != 1:
            ok = False
        below.append((str(wp_over_w), f"Gamma = {gamma[0]} + {gamma[1]} i"))
    above = []
    for wp_over_w, n in ((F(3, 5), F(4, 5)), (F(5, 13), F(12, 13)), (F(8, 17), F(15, 17))):
        if 1 - wp_over_w ** 2 != n ** 2:
            ok = False
        gamma = (1 - n) / (1 + n)
        T = 4 * n / (1 + n) ** 2
        if gamma ** 2 + T != 1:
            ok = False
        above.append((str(wp_over_w), str(gamma), str(T)))
    shell = []
    for w, ck, wp in ((F(5), F(4), F(3)), (F(13), F(12), F(5)), (F(17), F(8), F(15)), (F(25), F(24), F(7))):
        if w * w != wp * wp + ck * ck:
            ok = False
        K2 = (w + ck) / (w - ck)  # the light-cone boost (w - ck, w + ck) -> (K(w - ck), (w + ck)/K) that empties k
        if not is_square(K2):
            ok = False
            continue
        K = F(isqrt(K2.numerator), isqrt(K2.denominator))
        rest = ((w - ck) * K + (w + ck) / K) / 2, ((w + ck) / K - (w - ck) * K) / 2
        frame_velocity = (K2 - 1) / (K2 + 1)  # c = 1
        group, phase = ck / w, w / ck  # from 2 w dw = 2 c^2 k dk
        if rest != (wp, 0) or frame_velocity != group or group * phase != 1:
            ok = False
        shell.append((f"w={w} ck={ck}", f"rest frame {rest[0]} at velocity {frame_velocity}"))
    gap = True
    wp2, w02 = F(4), F(1)
    for w2 in (F(1), F(2), F(7, 2), F(4), F(5), F(8), F(17, 2)):
        cos_k = 1 - (w2 - wp2) / (2 * w02)
        if (-1 <= cos_k <= 1) != (wp2 <= w2 <= wp2 + 4 * w02):
            gap = False
    return ok and gap, {"rows below (wp/w, Gamma)": below, "rows above (wp/w, Gamma, T)": above,
                        "mass shell (w, ck): rest frequency, frame velocity = group velocity": shell,
                        "ladder passes exactly wp^2 <= w^2 <= wp^2 + 4 w0^2": gap}


def part_e():
    ok, rows = True, []
    for g in (F(1, 2), F(7, 8), F(99, 100)):
        k = (1 + g) / (1 - g)
        reads = {}
        for t in (F(0), F(1, 3), F(1, 2), F(1), F(2), None):
            u = (F(-1), F(0)) if t is None else ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
            rho = (g * u[0], g * u[1])
            one_minus = (1 - rho[0], -rho[1])
            mod2 = one_minus[0] ** 2 + one_minus[1] ** 2
            H = cdiv((F(1), F(0)), one_minus)
            s = (1 - u[0]) / 2  # the squared sine of half the round trip's phase
            if mod2 != (1 - g) ** 2 + 4 * g * s:
                ok = False
            P = cdiv((1 + rho[0], rho[1]), one_minus)[0]
            if P != (1 - g * g) / mod2 or (1 - g) ** 2 / mod2 != P / k:  # Fabry-Perot transmission (Airy) = P/k
                ok = False
            S, pw = (F(0), F(0)), (F(1), F(0))
            for m in range(1, 13):
                S = (S[0] + pw[0], S[1] + pw[1])
                pw = cmul(pw, rho)
                rem = cmul(pw, H)
                if (S[0] - H[0], S[1] - H[1]) != (-rem[0], -rem[1]) or pw[0] ** 2 + pw[1] ** 2 != g ** (2 * m):
                    ok = False
            reads["antiresonance" if t is None else str(t)] = P
        if reads["0"] != k or reads["antiresonance"] != 1 / k:
            ok = False
        rows.append((str(g), f"k = {k}", f"resonance {reads['0']}", f"antiresonance {reads['antiresonance']}"))
    return ok, rows


def part_f():
    ok, rows = True, []
    L = F(1)
    for c, u, w in ((F(5), F(3), F(4)), (F(13), F(5), F(12)), (F(25), F(7), F(24)), (F(17), F(8), F(15))):
        if c * c != u * u + w * w:
            ok = False
        along = L / (c - u) + L / (c + u)  # downwind out, upwind back
        across = 2 * L / w  # in the medium the sound aims upstream, velocity (-u, w); over the ground (0, w)
        if along != 2 * L * c / w ** 2 or along / across != c / w or not along > across:
            ok = False
        rows.append((f"c={c} u={u}", str(along), str(across), str(along / across)))
    return ok, rows


def main():
    fail = []
    for name, part in (("A", part_a), ("B", part_b), ("C", part_c), ("D", part_d), ("E", part_e), ("F", part_f)):
        ok, value = part()
        say(name, value)
        if not ok:
            fail.append(name)
    say("fail", fail)
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
