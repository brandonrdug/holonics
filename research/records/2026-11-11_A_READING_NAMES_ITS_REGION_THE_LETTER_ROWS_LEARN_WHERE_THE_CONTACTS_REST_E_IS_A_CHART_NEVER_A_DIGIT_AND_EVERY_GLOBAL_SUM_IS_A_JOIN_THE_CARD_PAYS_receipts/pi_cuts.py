"""Where each of the field's pi faces falls against its half unit, and the guard that decides it.

Simulates tower.rs half_turn (Machin, floor divisions, released once, half away from zero) and the
field's ring phasor angles and skin exponents (field.rs turn_phasor, skin_of) with Python integers,
against pi and ln 2 attained at 400 bits. A host ruler: it reads the code's faces, it is not the code.
"""
from fractions import Fraction

def release(x, bits):
    if bits == 0:
        return x
    half = 1 << (bits - 1)
    return (x + half) >> bits if x >= 0 else -((-x + half) >> bits)

def div_nearest(x, k):
    return (x + k // 2) // k if x >= 0 else -((-x + k // 2) // k)

def half_turn(bits, guard):
    one = 1 << (bits + guard)
    def atan_inverse(k):
        power, s, n = one // k, 0, 0
        while power != 0:
            term = power // (2 * n + 1)
            s += term if n % 2 == 0 else -term
            power //= k * k
            n += 1
        return s
    return release(16 * atan_inverse(5) - 4 * atan_inverse(239), guard)

W = 400
PI = Fraction(half_turn(W, 40), 1 << W)          # pi to about 400 bits
LN2 = Fraction(sum((1 << (W + 40 - k)) // k for k in range(1, W + 41)), 1 << (W + 40))

def nearest(q):                                   # half away from zero, q a Fraction
    return int((q + Fraction(1, 2)) // 1) if q >= 0 else -int((-q + Fraction(1, 2)) // 1)

def run_after_cut(q):
    """Distance of q's fraction from the half, and the run of equal bits after the cut."""
    f = q - (q.numerator // q.denominator)
    gap = abs(f - Fraction(1, 2))
    bits, x = [], f
    for _ in range(40):
        x *= 2
        b = int(x >= 1)
        bits.append(b)
        x -= b
    first = bits[0]
    run = next((i for i, b in enumerate(bits[1:], 1) if b != first), 40)
    return float(f), float(gap), run

# the field's rings: slots 16, reach 3771 (the line's declaration), periods by ring_periods
def tower(p, reach):
    out = [p]
    while out[-1] < reach:
        out.append(out[-1] * p)
    return out

def sample(t, count):
    if count == 1:
        return [t[-1]]
    return [t[k * (len(t) - 1) // (count - 1)] if count <= len(t) else t[k % len(t)] for k in range(count)]

reach, slots = 3771, 16
periods = sorted(sample(tower(2, reach), (slots + 1) // 2) + sample(tower(3, reach), slots // 2))
print("RING_PERIODS", " ".join(map(str, periods)))

if __name__ == "__main__":
    print("PI_CUT: the face of pi on 2^-bits, its fraction above the integer, its distance from the half, the run of")
    print("        equal bits after the cut, and the smallest guard (of 0 to 24) from which every guard returns the nearest")
    for bits in (30, 46, 60):
        q = PI * (1 << bits)
        truth = nearest(q)
        frac, gap, run = run_after_cut(q)
        ok = [g for g in range(25) if half_turn(bits, g) == truth]
        least = next(g for g in range(25) if all(half_turn(bits, h) == truth for h in range(g, 25)))
        print(f"PI_CUT bits={bits} fraction={frac:.4f} from_half={gap:.4f} run={run} guard_from={least} guard16_nearest={half_turn(bits, 16) == truth}")

    for guard in (16, 10, 8, 6, 4):
        pi46 = half_turn(46, guard)
        ln2_30 = release(sum((1 << (60 - k)) // k for k in range(1, 61)), 30)
        angle_off, angle_faces, angle_near = 0, 0, []
        skin_off, skin_live = 0, 0
        for n in periods:
            for r in range(min(n, reach)):
                c = r - n if 2 * r > n else r
                if c == 0 or 2 * c == n or 4 * c == n or 4 * c == -n:
                    continue                                   # the quarter points, held as identities
                angle_faces += 1
                theta30 = release(div_nearest(2 * pi46 * c, n), 16)
                exact = Fraction(2 * c, n) * PI * (1 << 30)
                if theta30 != nearest(exact):
                    angle_off += 1
                    angle_near.append((n, r))
            for d in range(reach):
                got = div_nearest(2 * pi46 * d, n * ln2_30)    # 2^-16, the skin's exponent in bits
                true_q = Fraction(2 * d, n) * PI / LN2 * (1 << 16)
                if got >> 16 <= 31:
                    skin_live += 1
                    if got != nearest(true_q):
                        skin_off += 1
        print(f"FIELD_FACES pi_guard={guard} pi46_nearest={pi46 == nearest(PI * (1 << 46))} angles={angle_faces} angles_not_nearest={angle_off} where={angle_near[:6]} skins_above_grain={skin_live} skins_not_nearest={skin_off}")
