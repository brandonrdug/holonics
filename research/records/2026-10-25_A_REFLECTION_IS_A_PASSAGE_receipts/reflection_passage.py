"""A reflection is a passage: exact checks of the moving mirror, two mirrors, the receding wall and a reactive wall.

Light-cone coordinates u = t - x, v = t + x (c = 1), as in lean/Holonics/Physics/Spacetime/Boost.lean, where
boost_k (u, v) = (k u, v / k) and the receiver of Doppler factor k has velocity (1/k, k).

A. A mirror at rest in the frame boost_k reflects (u, v) to R_k(u, v) = (v / k^2, k^2 u) (boost back, swap, boost).
   R_k is an involution, keeps uv and the pairing, fixes the mirror's worldline, keeps the future cone (time runs
   forward) and swaps its two null directions. A radar echo sent at t1 from x = 0 off the mirror x = beta t returns at
   t2 = k^2 t1 (Bondi), beta = (k^2 - 1)/(k^2 + 1).
B. The return is stretched: a right-moving wave of frequency w, its phase read on the mirror's worldline, leaves as a
   left-moving wave of frequency w / k^2 = w (1 - beta)/(1 + beta).
C. Two mirrors make a boost: R_k2 R_k1 = boost_((k1/k2)^2). Two Euclidean line reflections make a turn by twice the
   angle between them (rational points of the circle).
D. A box with one wall fixed at x = 0 and one receding, x = L0 + beta t: bounce events computed from the light rays,
   frequencies from the phase read on the wall. At every bounce w_n L_n is the same rational, and L_(n+1) / L_n =
   (1 + beta)/(1 - beta): the stretch is the wall's, bounce by bounce, for any |beta| < 1 (beta < 0 compresses).
E. A reactive wall, Gamma(x) = (i x - 1)/(i x + 1), x = w L / Z0 rational: |Gamma| = 1 (all of it returns) and
   Gamma^-1 dGamma/dx = -2i / (1 + x^2), a pure turn rate; its size, 2 L / Z0 at x = 0, is the delay of the return.
"""
import sys
import time
from fractions import Fraction as F

T0 = time.monotonic()


def say(part, value):
    print(part, f"elapsed_ms={int(1000 * (time.monotonic() - T0))}", value, flush=True)


def mirror(k, e):
    u, v = e
    return (v / k ** 2, k ** 2 * u)


def boost(k, e):
    u, v = e
    return (k * u, v / k)


def pairing(a, b):
    return -(a[0] * b[1] + a[1] * b[0]) / 2


def beta_of(k):
    return (k ** 2 - 1) / (k ** 2 + 1)


KS = [F(2), F(3), F(3, 2), F(5, 4), F(7, 3), F(1, 2)]
EVENTS = [(F(a), F(b)) for a in range(-3, 4) for b in range(-3, 4)] + [(F(1, 3), F(5, 7)), (F(-2, 9), F(4, 5))]


def part_a():
    ok = {"involution": True, "uv kept": True, "pairing kept": True, "worldline fixed": True,
          "future cone kept": True, "null axes swapped": True, "radar t2 = k^2 t1": True}
    for k in KS:
        for e in EVENTS:
            if mirror(k, mirror(k, e)) != e:
                ok["involution"] = False
            r = mirror(k, e)
            if r[0] * r[1] != e[0] * e[1]:
                ok["uv kept"] = False
            for g in EVENTS[:9]:
                if pairing(mirror(k, e), mirror(k, g)) != pairing(e, g):
                    ok["pairing kept"] = False
            if e[0] > 0 and e[1] > 0 and not (r[0] > 0 and r[1] > 0):
                ok["future cone kept"] = False
        for tau in (F(1), F(5, 2), F(-3)):
            w = (tau / k, tau * k)
            if mirror(k, w) != w:
                ok["worldline fixed"] = False
        if mirror(k, (F(1), F(0))) != (F(0), k ** 2) or mirror(k, (F(0), F(1))) != (1 / k ** 2, F(0)):
            ok["null axes swapped"] = False
        b = beta_of(k)
        for t1 in (F(1), F(7, 3)):
            # emitted at (t1, 0): u = t1; the mirror x = b t meets the ray x = t - t1 at t = t1 / (1 - b)
            tm = t1 / (1 - b)
            xm = b * tm
            t2 = tm + xm  # the left-moving ray back to x = 0
            if t2 != k ** 2 * t1:
                ok["radar t2 = k^2 t1"] = False
    return ok


def part_b():
    ok = True
    rows = []
    for k in KS:
        b = beta_of(k)
        w = F(5)
        # the incoming phase w (t - x) on the mirror's worldline x = b t, read as a function of v = t + x
        t_a, t_b = F(1), F(4)
        phase = [w * (t - b * t) for t in (t_a, t_b)]
        vs = [t + b * t for t in (t_a, t_b)]
        w_out = (phase[1] - phase[0]) / (vs[1] - vs[0])
        rows.append((str(k), str(w_out / w)))
        if w_out != w / k ** 2 or w_out != w * (1 - b) / (1 + b):
            ok = False
    return {"stretch 1/k^2 = (1-beta)/(1+beta)": ok, "ratios": rows}


def part_c():
    ok_l = all(mirror(k2, mirror(k1, e)) == boost((k1 / k2) ** 2, e) for k1 in KS for k2 in KS for e in EVENTS)
    # Euclidean: the reflection in the line at angle a is [[c, s], [s, -c]], (c, s) = (cos 2a, sin 2a) rational
    pts = [(F(1), F(0)), (F(3, 5), F(4, 5)), (F(5, 13), F(12, 13)), (F(-8, 17), F(15, 17))]

    def refl(p):
        c, s = p
        return ((c, s), (s, -c))

    def mul(a, b):
        return tuple(tuple(sum(a[i][m] * b[m][j] for m in range(2)) for j in range(2)) for i in range(2))

    ok_e = True
    for p1 in pts:
        for p2 in pts:
            m = mul(refl(p2), refl(p1))
            # the turn by twice the angle between the lines: (cos, sin) of 2(a2 - a1) = p2 * conj(p1)
            c = p2[0] * p1[0] + p2[1] * p1[1]
            s = p2[1] * p1[0] - p2[0] * p1[1]
            if m != ((c, -s), (s, c)):
                ok_e = False
    return {"two Lorentzian mirrors = boost (k1/k2)^2": ok_l, "two Euclidean reflections = turn": ok_e}


def part_d(beta, bounces=40):
    L0, s, w = F(1), F(0), F(3)
    invariant, ratios, ok = None, set(), True
    first_L, last_L = None, None
    for _ in range(bounces):
        tw = (s + L0) / (1 - beta)  # the right-moving ray x = t - s meets x = L0 + beta t
        xw = L0 + beta * tw
        # frequency after the bounce: the phase w (t - x) on the wall's worldline, read in v = t + x
        t1, t2 = tw, tw + 1
        ph = [w * (t - (L0 + beta * t)) for t in (t1, t2)]
        vv = [t + (L0 + beta * t) for t in (t1, t2)]
        w_after = (ph[1] - ph[0]) / (vv[1] - vv[0])
        if invariant is None:
            invariant = w * xw
        elif w * xw != invariant:
            ok = False
        if last_L is not None:
            ratios.add(xw / last_L)
        else:
            first_L = xw
        last_L = xw
        w = w_after
        s = tw + xw  # the left-moving ray reaches x = 0 and leaves again at once
    return {"beta": str(beta), "w L constant": ok, "L ratios": sorted(str(r) for r in ratios),
            "expected ratio": str((1 + beta) / (1 - beta)), "invariant": str(invariant), "first L": str(first_L),
            "last L = first L * ratio^(bounces - 1)": last_L == first_L * ((1 + beta) / (1 - beta)) ** (bounces - 1)}


def part_e():
    ok = True
    for x in (F(0), F(1, 2), F(1), F(3), F(-2, 7)):
        g = complex_rat_div((-1, x), (1, x))  # (i x - 1)/(i x + 1) as (re, im)
        if g[0] ** 2 + g[1] ** 2 != 1:
            ok = False
        # Gamma^-1 dGamma/dx = i/(ix - 1) - i/(ix + 1)
        a = complex_rat_div((0, F(1)), (-1, x))
        b = complex_rat_div((0, F(1)), (1, x))
        ld = (a[0] - b[0], a[1] - b[1])
        if ld != (F(0), F(-2) / (1 + x * x)):
            ok = False
    return {"|Gamma| = 1 and Gamma^-1 dGamma/dx = -2i/(1+x^2)": ok, "delay at x = 0, units L/Z0": "2"}


def complex_rat_div(a, b):
    ar, ai = F(a[0]), F(a[1])
    br, bi = F(b[0]), F(b[1])
    d = br * br + bi * bi
    return ((ar * br + ai * bi) / d, (ai * br - ar * bi) / d)


def main():
    fail = []
    a = part_a()
    say("A", a)
    fail += [f"A {k}" for k, v in a.items() if not v]
    b = part_b()
    say("B", b)
    if not b["stretch 1/k^2 = (1-beta)/(1+beta)"]:
        fail.append("B")
    c = part_c()
    say("C", c)
    fail += [f"C {k}" for k, v in c.items() if not v]
    for beta in (F(1, 3), F(1, 7), F(2, 5), F(-1, 3)):
        d = part_d(beta)
        say("D", d)
        if not d["w L constant"] or d["L ratios"] != [d["expected ratio"]] or not d["last L = first L * ratio^(bounces - 1)"]:
            fail.append(f"D {beta}")
    e = part_e()
    say("E", e)
    if not e["|Gamma| = 1 and Gamma^-1 dGamma/dx = -2i/(1+x^2)"]:
        fail.append("E")
    say("fail", fail)
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
