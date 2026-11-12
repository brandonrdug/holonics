#!/usr/bin/env -S python3 -I
"""u1_reach_ruler.py: every reach of the line's field on one scale of ranges, beside each part's turn defect (the record's
§9, U1: before the next founding, "a host ruler from the declaration lists every reach in the field on one scale of ranges
(the skins at n/2π, the near field, the carry at (1 + d)/d, the shells by octave, which have none) beside each part's turn
defect").

The scale. A part that carries a place's state one place on at the multiplier mu has the range R = sum_(k>=0) |mu|^k =
1/(1 - |mu|) places, the mean age of what it hears: the carry's (1 + d)/d (atlas contact.carried-product-group-size), a
skin's 1/(1 - e^(-2pi/n)), about n/2pi + 1/2. A hard window of w places has the range w. A part that keeps modulus one hears
the whole region. The shells are an address and carry no range.

The turn defect. A face whose turn leaves the unit disk boosts as it turns (the region record §5c; §14.3 here): the ruler
counts each part's faces outside the disk on its own route and the largest excess, in units of 2^-60 of |z|^2, and reads
whether any read the field makes stands outside the disk once the part's friction or skin is applied.

A host ruler: Python integers reproducing the routes of field.rs (turn_phasor; skin_of up to its exponent; carry_gate,
carry_coupling and carry_friction at a given friction) and tower.rs (half_turn, exp_series), with pi and ln 2 attained at 400
bits. It reads the declaration and, where given, receipts' FIELD_CARRY_GATES lines (modulus_mean on 2^-30 by circle); it is
not the code. Floats only to print a range.

  u1_reach_ruler.py [HEAD_LINE] [--gates LABEL=FILE[:LAP] ...]
"""
import math
import sys

MOVE = 30          # the frames' grain, 2^-30 (field.rs MOVE_BITS)
PACE = 24          # the pace's grain, 2^-24 (PACE_BITS)
FACE = 16          # the face's grain, 2^-16 (FACE_BITS)
NEAR = 6           # field.rs NEAR: 0 < |i - j| < lcm(2, 3)
LINE = "hnn-field-v14e 100 64 4 8 2 128 4 4 3771 2 0 32"   # the carry line's head (te1, te2)


def release(x, bits):
    if bits == 0:
        return x
    half = 1 << (bits - 1)
    return (x + half) >> bits if x >= 0 else -((-x + half) >> bits)


def div_nearest(x, k):
    return (x + k // 2) // k if x >= 0 else -((-x + k // 2) // k)


def half_turn(bits, guard=16):
    """tower.rs half_turn: Machin's formula on floor divisions, released once."""
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


def ln2_face():
    """field.rs ln2_face: ln 2 on 2^-30, from its series on 2^-60 released once."""
    return release(sum((1 << (60 - k)) // k for k in range(1, 61)), 30)


def exp_series(a, b):
    """tower.rs exp_series: e^(a + ib) on 2^-30 for a and b on 2^-30, each term released to the grain."""
    term = (1 << MOVE, 0)
    s = term
    k = 1
    while True:
        re = release(term[0] * a - term[1] * b, MOVE)
        im = release(term[0] * b + term[1] * a, MOVE)
        term = (div_nearest(re, k), div_nearest(im, k))
        if term == (0, 0):
            return s
        s = (s[0] + term[0], s[1] + term[1])
        k += 1


def turn_phasor(rho, n, pi46):
    """field.rs turn_phasor: e^(2 pi i rho/n) on 2^-30, rho on 2^-24, the quarter points held exactly."""
    one = 1 << MOVE
    period = n << PACE
    r = rho % period
    c = r - period if 2 * r > period else r
    if c == 0:
        return (one, 0)
    if 2 * c == period:
        return (-one, 0)
    if 4 * c == period:
        return (0, one)
    if 4 * c == -period:
        return (0, -one)
    theta = div_nearest(2 * pi46 * c, period)
    return exp_series(0, release(theta, 16))


def skin_bits(d, n, pi46, ln2):
    """field.rs skin_of up to its exponent: 2 pi d/(n ln 2) bits on 2^-16 at a whole distance d."""
    return div_nearest(2 * pi46 * (d << PACE), (n * ln2) << PACE)


def tower(p, reach):
    out = [p]
    while out[-1] < reach:
        out.append(out[-1] * p)
    return out


def ring_periods(slots, reach):
    """field.rs ring_periods: the dyadic and triadic towers sampled to the slots, sorted."""
    def sample(t, count):
        if count == 1:
            return [t[-1]]
        return [t[k * (len(t) - 1) // (count - 1)] if count <= len(t) else t[k % len(t)] for k in range(count)]
    return sorted(sample(tower(2, reach), (slots + 1) // 2) + sample(tower(3, reach), slots // 2))


def declaration(line):
    w = line.split()
    assert w[0] in ("hnn-field-v14", "hnn-field-v14e"), "a field's head line"
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(v) for k, v in zip(names, w[1:11])}
    d["depth"] = int(w[11]) if len(w) > 11 else 0
    d["carry"] = int(w[12]) if w[0] == "hnn-field-v14e" else 0
    return d


def carry_gate(q, d):
    """field.rs carry_gate at a friction d on 2^-16 (carry_friction's result): gamma on 2^-30."""
    turn = (1 << 34) + q * q
    den = turn * ((1 << 16) + d)
    return (div_nearest(((1 << 34) - q * q) << 46, den), div_nearest(q << 64, den))


def carry_coupling(d):
    """field.rs carry_coupling: kappa = N0 d/(1 + d) on 2^-30, N0 = NEAR - 1."""
    return div_nearest(((NEAR - 1) * d) << MOVE, (1 << FACE) + d)


def gates_line(path, lap):
    """modulus_mean by circle (2^-30) from the FIELD_CARRY_GATES line of a receipt at the given lap (the last one if None)."""
    found = None
    for line in open(path):
        if line.startswith("FIELD_CARRY_GATES"):
            words = dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)
            if lap is None or words.get("lap") == lap:
                found = [int(x) for x in words["modulus_mean"].split("/")]
    assert found, f"no FIELD_CARRY_GATES line at lap {lap} in {path}"
    return found


def main():
    args = sys.argv[1:]
    gates = []
    while "--gates" in args:
        k = args.index("--gates")
        label, spec = args[k + 1].split("=", 1)
        path, _, lap = spec.partition(":")
        gates.append((label, path, lap or None))
        del args[k:k + 2]
    d = declaration(" ".join(args) if args else LINE)
    pi46, ln2 = half_turn(46), ln2_face()
    reach, one = d["reach"], 1 << MOVE
    slots = (d["frames"] - d["still"]) * d["modes"]
    periods = ring_periods(slots, reach)
    print(f"# the declaration: {' '.join(args) if args else LINE}; turned slots {slots}, ring periods {' '.join(map(str, periods))}")
    print("# REACH part= range= (places, R = 1/(1 - |mu|) for a one-place multiplier mu, a window's count, or the region) turn_defect=")

    # The strand: a pair contact's strand mate and the opening's two contact rows, one place each side.
    print("REACH part=strand range=1 what=the_pair_contact's_strand_mate_(t-1_even,_t+1_odd)_and_the_opening's_E-_E+_rows "
          "turn_defect=none_(a_product_of_two_sites'_reads,_no_turn)")

    # The near field: 0 < |i - j| < NEAR through every head, each source at its address cost of floor(log2 d) bits.
    near = NEAR - 1
    weighted = sum(2.0 ** -int(math.log2(k)) for k in range(1, NEAR))
    print(f"REACH part=near range={near} window=0<|i-j|<{NEAR} weights_at_the_address_cost_sum={weighted:.2f} "
          "turn_defect=its_heads'_(a_still_head's_none,_a_turned_head's_its_rings')")
    print(f"REACH part=ticks range={d['ticks'] * near} what={d['ticks']}_ticks_of_the_near_field_each_side,_hop_by_hop turn_defect=-")

    # The carry circles: gamma = turn(q)/(1 + d), d = d0 2^l, the range (1 + d)/d.
    if d["carry"]:
        d0 = (1 << FACE) // (NEAR - 2)
        g0 = carry_gate(0, d0)
        k0 = carry_coupling(d0)
        r0 = one / (one - g0[0])
        print(f"REACH part=carry state=founded d={d0}/2^16 range={r0:.4f} gamma={g0[0]}/2^30 kappa={k0}/2^30 "
              f"(kappa_at_the_founding_is_2^30:{k0 == one})")
        print(f"REACH part=carry state=friction_floor d=1/2^16 range={(1 << FACE) + 1} what=the_most_a_circle_holds")
        print(f"REACH part=carry state=friction_carrier d<2^47/2^16 range={1 + (1 << FACE) / (1 << 47):.6f} what=the_least_before_refusal")
        # The turn defect: the gate's modulus over q at frictions from the floor up, against the disk, and the turn alone.
        worst_gate, worst_turn, tried = -(1 << 70), -(1 << 70), 0
        qs = {0}
        for k in range(0, 39):
            for x in ((1 << k) - 1, 1 << k, (1 << k) + 1, 3 << max(k - 1, 0), (5 << k) // 3):
                if 0 <= x < 1 << 39:
                    qs.update((x, -x))
        for q in sorted(qs):
            if (1 << 34) + q * q >= 1 << 78:
                continue
            for fr in (1, 2, 3, 1 << 8, d0, 1 << 20, (1 << 31) - 1):
                g = carry_gate(q, fr)
                m = g[0] ** 2 + g[1] ** 2
                worst_gate = max(worst_gate, m - (1 << 60))
                # the turn alone at the friction's floor, |gamma| (1 + d) on the disk's scale with the friction divided back out
                # (at a larger friction the gate's rounding is a larger share of a smaller gate, and the turn is never applied alone)
                if fr == 1:
                    t = m * ((1 << FACE) + fr) ** 2
                    worst_turn = max(worst_turn, t - (1 << (60 + 2 * FACE)))
                tried += 1
        print(f"REACH part=carry turn_defect: over {tried} gates (q from 0 to 2^39 either sign, frictions from the floor to the carrier) "
              f"the largest |gamma|^2 - 2^60 = {worst_gate} (inside the disk: {worst_gate < 0}, by {-worst_gate / (1 << 60):.3g} of it at the "
              f"floor); the turn alone at the floor, |gamma|^2 (1 + d)^2 - 2^60 = {worst_turn / (1 << (2 * FACE)):.1f} units of 2^-60 "
              f"(the Cayley step keeps the circle, so its rounding is all its defect, and the friction covers it {-worst_gate / max(1.0, worst_turn / (1 << (2 * FACE))):.3g} times)")
        for label, path, lap in gates:
            mm = gates_line(path, lap)
            rs = [one / (one - m) for m in mm]
            mean_mod = sum(mm) / len(mm) / one
            print(f"REACH part=carry state=read:{label} circles={len(mm)} mean_|gamma|={mean_mod:.4f} range_at_the_mean_|gamma|={1 / (1 - mean_mod):.2f} "
                  f"range_by_circle_min/mean/max={min(rs):.1f}/{sum(rs) / len(rs):.1f}/{max(rs):.1f}")

    # The rings: a turned mode reads e^(2 pi i r/n) with the skin e^(-2 pi d/n); a still mode U = 1 with no skin.
    if d["still"]:
        print(f"REACH part=still heads={d['still']}_of_{d['frames']}_ring_sets range={reach} what=no_skin:_the_word_at_any_distance_in_the_region,"
              "_far_sources_met_by_class_at_floor(log2_d)_bits turn_defect=0_(U_=_1_held_exactly)")
    total_faces, total_out = 0, 0
    for n in periods:
        bits1 = skin_bits(1, n, pi46, ln2)
        mu = 2.0 ** (-bits1 / (1 << FACE))
        rng = 1.0 / (1.0 - mu)
        heard = next((k - 1 for k in range(1, reach + 1) if skin_bits(k, n, pi46, ln2) >> FACE > 31), reach)
        mu30 = round(mu * one)  # the skin's face at d = 1 on 2^-30, to print and to price the defect against
        faces, out, worst, worst_skinned = 0, 0, -(1 << 70), -(1 << 130)
        for r in range(min(n, reach)):
            c = r - n if 2 * r > n else r
            if c == 0 or 2 * c == n or 4 * c == n or 4 * c == -n:
                continue
            z = turn_phasor(r << PACE, n, pi46)
            m = z[0] ** 2 + z[1] ** 2
            faces += 1
            if m > 1 << (2 * MOVE):
                out += 1
            worst = max(worst, m - (1 << (2 * MOVE)))
            worst_skinned = max(worst_skinned, m * mu30 * mu30 - (1 << (4 * MOVE)))
        total_faces += faces
        total_out += out
        if faces:
            defect = (f"faces_outside_the_disk={out}/{faces} largest_excess={worst}/2^60 boost_a_read={worst / (1 << 61):.2e}_nats "
                      f"with_the_skin_at_d=1_inside_the_disk={worst_skinned < 0} by={-worst_skinned / (1 << (4 * MOVE)):.3g}")
        else:
            defect = "none_(every_face_a_quarter_point,_held_exactly)"
        print(f"REACH part=skin ring={n} range={rng:.2f} n/2pi={n / (2 * math.pi):.2f} heard_to={heard} turn_defect: {defect}")
    print(f"REACH part=rings faces={total_faces} outside_the_disk={total_out}")
    if d["depth"]:
        print(f"REACH part=depth rings={d['depth']} range={reach} what=|mu|_=_1:_relative_depth_at_any_span turn_defect=its_rings'")
    shells = 0
    while 9 ** shells < reach:      # field.rs class_trits: the least k with 9^k >= reach, at most the modes
        shells += 1
    shells = min(d["modes"], shells)
    print(f"REACH part=shells trits_a_head={shells} range=none what=an_address_by_octave,_not_a_reach turn_defect=-")
    print(f"REACH part=region range={reach} what=the_most_sites_a_region_spans")


if __name__ == "__main__":
    main()
