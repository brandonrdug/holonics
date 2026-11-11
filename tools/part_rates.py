#!/usr/bin/env -S python3 -I
"""part_rates.py: the founded parts' deposit rates, moved between laps from saved states (host arithmetic: no card, no model).

  part_rates.py open STATE CONTACTS_BEFORE OCTAVES OUT
  part_rates.py update OLDER OLD NOW OUT
  part_rates.py means OLDER OLD NOW STATE OUT    (theory, November 11: the same rule read on lap means; see below)
  part_rates.py trend OLDEST OLDER OLD NOW OUT   (theory, November 11 03:54: the slope-corrected rule; see trend())
  part_rates.py base STATE RATE_BITS OUT         (theory, November 11: the learner's own rate word; see below)
  part_rates.py polar MEAN_A MEAN_B MEAN_C MEAN_D STATE OUT [SECTIONS SITES]   (theory, November 11 21:15, G86: a part's rate follows its
                                                 polarization; see polar())

The learner's text carries each founded part's octaves in a trailing `parts CONTACTS_BEFORE k0 .. k15` line (holonics::hnn::tower::field::
RateParts), and `.. k18` where the field has carry circles (theory, November 11 17:25: the circles' charts `carry`, their W columns
`w_carry`, their a and b rows `a_carry`, `b_carry`); the trainer steps part p at 2^-(rate - k_p). A line of fifteen or sixteen reads with the
parts it lacks at octave 0, and a state without carry circles writes and prints sixteen. `open` writes STATE with the octaves OCTAVES
(sixteen counts, fifteen with `carry` at the old rate, or nineteen, comma separated, in PART_NAMES order). `update` reads three saved states of one line and, for each part, the cosine c between its displacements OLD - OLDER and
NOW - OLD over the entries it holds (exact integers): c > 1/2 one octave faster, c < 1/2 one slower, never under the old rate (octave 0) nor
past rate - 1; c = 1/2 rests. It writes NOW with the moved octaves to OUT and prints FIELD_PART_RATE for every part. The parts are
Field::founded_parts' (checked against it by the ignored test founded_parts_and_their_cosines_on_saved_states). Numbers only.

`means` reads the cosines from three lap means of one line (the trainer's MEAN.{lap}, or any three materials of one declaration) and
moves the octaves that STATE carries, the lap's end state the next lap trains from: it writes STATE, every line and its material, with
the moved octaves to OUT. Reason (the record of November 11 on a deposit's rate as a temperature): a lap's end state is one draw of the
rate's standing spread, so between lap ends a part's cosine is (d^2 - s^2) / (d^2 + 2 s^2) for a lap's travel d and end draws of
variance s^2, and a part that travels steadily under a large spread reads as one at rest; a lap's mean sheds the spread of every
direction that relaxes inside the lap. The three materials are read only; OUT is a state a tool wrote, checked before a lap trains
from it. Controls: tools/test_part_rates.py.

`base` writes STATE with the learner's rate word (the second word of its first line, which the trainer reads from the state and
steps every entry of no founded part at, 2^-RATE_BITS; a founded part steps at 2^-(RATE_BITS - k_p)) set to RATE_BITS, and every other
word, line and the material as they stand. One bit fewer is the whole machine one octave hotter, parts and old entries alike, which no
octave line can say (an octave is never under 0). It refuses a rate that leaves a part's octave at or past it. OUT is a state a tool
wrote, checked before a lap trains from it.
"""
import sys
from math import isqrt

PART_NAMES = ["w_new", "a_new", "b_new", "enc_lane", "before_lane", "after_lane", "q_lane", "v_lane", "probe_lane", "out_lane", "moment_face_lane", "read_lane", "face_biases_lane", "a_lane", "b_lane", "carry", "w_carry", "a_carry", "b_carry", "enc_first", "before_first", "after_first"]
PARTS = len(PART_NAMES)
PLAIN_PARTS = 16  # the plain parts every field writes
CIRCLE_PARTS = list(range(16, 19))  # the carry circles' three, written only where the field has circles
FIRST_PARTS = list(range(19, 22))  # the first lane's letter rows' three (theory, November 11 21:15, G86), written by every field


def written(d):
    """The parts a state of declaration d writes and prints, in the line's order (holonics::hnn::tower::field::written_parts): the plain
    sixteen, the circles' three where it has circles, then the first lane's letter rows' three."""
    return list(range(PLAIN_PARTS)) + (CIRCLE_PARTS if d.get("carry", 0) > 0 else []) + FIRST_PARTS


def expand(d, v):
    """A parts line's octaves (without its contacts count) as all PARTS, by the line's order for d: a line of the written length is the
    written parts in order; an older one (fifteen or sixteen, or nineteen with carry circles) is the parts before the letter rows', the
    ones it lacks at octave 0."""
    order = written(d)
    older = list(range(PLAIN_PARTS)) + (CIRCLE_PARTS if d.get("carry", 0) > 0 else [])
    if len(v) == len(order):
        slots = order
    elif len(v) in (len(older), PLAIN_PARTS, PLAIN_PARTS - 1):
        slots = older[:len(v)]
    else:
        raise AssertionError(f"a parts line of {len(v)} parts, neither the written {len(order)} nor an older count")
    out = [0] * PARTS
    for slot, k in zip(slots, v):
        out[slot] = k
    return out
OLD = -1


def layout(d):
    a, dw, heads, modes, still, f, frames = d["alphabet"], d["width"], d["heads"], d["modes"], d["still"], d["contacts"], d["frames"]
    m2 = 2 * heads * modes
    tm = sum(1 for h in range(heads) if h % frames >= still) * modes
    paced = sum(1 for h in range(heads) if h % frames >= still)
    fam, at = {}, 0

    def push(name, n):
        nonlocal at
        fam[name] = at
        at += n

    push("enc", (a + 1) * dw); push("before", (a + 1) * dw); push("after", (a + 1) * dw)
    push("q", m2 * dw); push("q_bias", m2); push("v", m2 * dw); push("v_bias", m2)
    push("out", dw * m2); push("out_bias", dw)
    push("a", f * dw); push("a_bias", f); push("b", f * dw); push("b_bias", f)
    push("w", dw * f); push("w_bias", dw)
    push("read", dw * dw); push("read_bias", a)
    push("moment_before", (a + 1) * 2 * tm); push("moment_after", (a + 1) * 2 * tm)
    push("temper", 2 * heads)
    push("probe", m2 * dw); push("probe_bias", m2)
    push("pace", paced * (a + 1))
    push("moment_face", dw * m2); push("moment_face_bias", dw); push("lift_bias", dw)
    c = d.get("carry", 0)
    if c > 0:
        push("carry", 2 * c * dw); push("carry_bias", 2 * c)
    return fam, at


def founded_parts(d, contacts_before):
    """Field::founded_parts: each entry's part index, OLD where it is none."""
    fam, total = layout(d)
    dw, f, m2, a1 = d["width"], d["contacts"], 2 * d["heads"] * d["modes"], d["alphabet"] + 1
    lw = dw // d["lanes"] if d["lanes"] > 1 else dw
    half_old, half_new = contacts_before // 2, f // 2
    new_contact = lambda e: half_old <= e < half_new or e >= half_new + half_old
    parts = [OLD] * total
    for part, name in ((3, "enc"), (4, "before"), (5, "after")):
        for r in range(a1):
            for c in range(lw, dw):
                parts[fam[name] + r * dw + c] = part
    for part, name in ((6, "q"), (7, "v"), (8, "probe")):
        for r in range(m2):
            for c in range(lw, dw):
                parts[fam[name] + r * dw + c] = part
    for part, name in ((9, "out"), (10, "moment_face")):
        for i in range(lw * m2, dw * m2):
            parts[fam[name] + i] = part
    for r in range(dw):
        for c in range(dw):
            if r >= lw or c >= lw:
                parts[fam["read"] + r * dw + c] = 11
    for name in ("out_bias", "w_bias", "moment_face_bias", "lift_bias"):
        for i in range(lw, dw):
            parts[fam[name] + i] = 12
    for part, name in ((13, "a"), (14, "b")):
        for e in range(f):
            for c in range(lw, dw):
                parts[fam[name] + e * dw + c] = part
    for e in range(f):
        if new_contact(e):
            for part, name, bias in ((1, "a", "a_bias"), (2, "b", "b_bias")):
                for c in range(dw):
                    parts[fam[name] + e * dw + c] = part
                parts[fam[bias] + e] = part
            for r in range(dw):
                parts[fam["w"] + r * f + e] = 0
    # The first lane's letter rows (theory, November 11 21:15, G86): the encodings' columns over the first lane.
    for part, name in ((FIRST_PARTS[0], "enc"), (FIRST_PARTS[1], "before"), (FIRST_PARTS[2], "after")):
        for r in range(a1):
            for c in range(lw):
                parts[fam[name] + r * dw + c] = part
    # The carry circles', over the lane's and the new contacts': their charts and biases, their W columns, their a and b rows with the biases.
    c = d.get("carry", 0)
    if c > 0:
        for i in range(2 * c * dw):
            parts[fam["carry"] + i] = 15
        for i in range(2 * c):
            parts[fam["carry_bias"] + i] = 15
        for e0 in range(f // 2 - c, f // 2):
            for e in (e0, f // 2 + e0):
                for r in range(dw):
                    parts[fam["w"] + r * f + e] = 16
                for part, name, bias in ((17, "a", "a_bias"), (18, "b", "b_bias")):
                    for j in range(dw):
                        parts[fam[name] + e * dw + j] = part
                    parts[fam[bias] + e] = part
    return parts


def load(path):
    lines = open(path).read().split("\n")
    words = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(w) for k, w in zip(names, words[1:11])}
    assert words[0] != "hnn-field-v14k", "the carry founded at zero friction is retired (hnn-field-v14k): its states are receipts only"
    assert (words[0], len(words)) in (("hnn-field-v14", 12), ("hnn-field-v14t", 13), ("hnn-field-v13", 11)), "a field's head line that is not hnn-field-v14"
    d["carry"] = int(words[12]) if words[0] == "hnn-field-v14t" else 0
    rate = int(lines[0].split(" ")[1])
    theta = [int(x) for x in lines[2].split(" ")]
    return lines, d, rate, theta


def parts_line(lines, d):
    """A state's parts line as (contacts_before, all PARTS octaves), read by d's order (expand); None without one."""
    for l in lines:
        if l.startswith("parts "):
            v = [int(x) for x in l.split(" ")[1:]]
            return v[0], expand(d, v[1:])
    return None


def write(lines, d, contacts_before, octaves, out):
    kept = [l for l in lines if not l.startswith("parts ")]
    while kept and kept[-1] == "":
        kept.pop()
    kept.append("parts " + " ".join(str(x) for x in [contacts_before] + [octaves[p] for p in written(d)]))
    with open(out, "x") as f:
        f.write("\n".join(kept) + "\n")


def micro(num, den):
    """floor-toward-zero of 10^6 num / den, exact (den > 0)."""
    q = abs(num) * 1_000_000 // den
    return -q if num < 0 else q


def main():
    args = sys.argv[1:]
    if len(args) == 5 and args[0] == "open":
        lines, d, rate, _ = load(args[1])
        contacts_before, octaves = int(args[2]), [int(k) for k in args[3].split(",")]
        octaves = expand(d, octaves)
        assert all(0 <= k < rate for k in octaves), "octave counts each under the rate's bits"
        assert 0 < contacts_before <= d["contacts"] and contacts_before % 4 == 0
        parts = founded_parts(d, contacts_before)
        for p in written(d):
            print(f"FIELD_PART_RATE part={PART_NAMES[p]} entries={parts.count(p)} c=- rate_octaves={octaves[p]} rate_bits={rate - octaves[p]}")
        write(lines, d, contacts_before, octaves, args[4])
    elif (len(args) == 5 and args[0] == "update") or (len(args) == 6 and args[0] == "means"):
        (_, da, ra, older), (_, db, rb, old), (lines, dc, rate, now) = load(args[1]), load(args[2]), load(args[3])
        if args[0] == "means":
            # The octaves moved, and every line written, are the lap's end state's; the three materials above give the cosines alone.
            lines, dt, rate, target = load(args[4])
            assert dt == dc and len(target) == len(now), "the state the octaves move in is of the means' declaration"
        assert da == db == dc and len(older) == len(old) == len(now), "three states of one declaration"
        held = parts_line(lines, dc)
        assert held is not None, "a state with no founded parts' rates (open sets them)"
        contacts_before, octaves = held
        parts = founded_parts(dc, contacts_before)
        assert len(parts) == len(now)
        dot, first, second, entries = [0] * PARTS, [0] * PARTS, [0] * PARTS, [0] * PARTS
        for i, p in enumerate(parts):
            if p == OLD:
                continue
            d1, d2 = old[i] - older[i], now[i] - old[i]
            entries[p] += 1
            dot[p] += d1 * d2
            first[p] += d1 * d1
            second[p] += d2 * d2
        nxt = list(octaves)
        for p in written(dc):
            name = PART_NAMES[p]
            k = octaves[p]
            if first[p] == 0 or second[p] == 0 or dot[p] <= 0:
                side = -1
            else:
                lhs, rhs = 4 * dot[p] * dot[p], first[p] * second[p]
                side = (lhs > rhs) - (lhs < rhs)
            k2 = min(k + 1, rate - 1) if side > 0 else (max(k - 1, 0) if side < 0 else k)
            nxt[p] = k2
            root = isqrt(first[p] * second[p])
            c = micro(dot[p], root) if root > 0 else 0
            move = "faster" if k2 > k else "slower" if k2 < k else "hold"
            print(f"FIELD_PART_RATE part={name} entries={entries[p]} c={'-' if c < 0 else ''}{abs(c) // 1_000_000}.{abs(c) % 1_000_000:06d} rate_octaves={k2} was={k} move={move} rate_bits={rate - k2}")
        write(lines, dc, contacts_before, nxt, args[-1])
    elif len(args) == 6 and args[0] == "trend":
        trend(args[1:5], args[5])
    elif len(args) in (7, 9) and args[0] == "polar":
        polar(args[1:5], args[5], args[6], *(int(x) for x in args[7:9]))
    elif len(args) == 4 and args[0] == "base":
        lines, d, rate, _ = load(args[1])
        bits = int(args[2])
        head = lines[0].split(" ")
        assert head[0] == "hnn-field-learner-v3" and len(head) == 5 and head[4] == "-", "a learner's text with no held step"
        held = parts_line(lines, d)
        octaves = held[1] if held is not None else [0] * PARTS
        assert bits >= 1 and all(k < bits for k in octaves), "a rate of one bit or more, past every part's octave"
        head[1] = str(bits)
        print(f"FIELD_BASE_RATE was={rate} rate_bits={bits} octaves_hotter={rate - bits}")
        if held is not None:
            parts = founded_parts(d, held[0])
            for p in written(d):
                print(f"FIELD_PART_RATE part={PART_NAMES[p]} entries={parts.count(p)} c=- rate_octaves={octaves[p]} rate_bits={bits - octaves[p]}")
        with open(args[3], "x") as f:
            f.write("\n".join([" ".join(head)] + lines[1:]))
    else:
        sys.exit(__doc__)


GRAIN = 40  # the cosines, their slope and the noise term are released at 2^-40 (floor), a declared width; a tie at the grain rests


def octave_of(ratio):
    """The octave nearest log2(ratio), in rationals: the o with 2^(o - 1/2) <= ratio < 2^(o + 1/2), read on squares, 2^(2o - 1) <= ratio^2 <
    2^(2o + 1), so the edges (irrational) are never met by a rational ratio and no float decides it. ratio is a positive Fraction."""
    from fractions import Fraction
    sq = ratio * ratio
    o = 0
    while Fraction(2) ** (2 * o + 1) <= sq:
        o += 1
    while Fraction(2) ** (2 * o - 1) > sq:
        o -= 1
    return o


def polar_octaves(heat, heat_base, fall, rate_bits):
    """[definition; theory, November 11 21:15, G86] The law's decision, in rationals (Fraction), with no float. heat, heat_base and fall map each part (and the
    old entries, key OLD) to its Fractions: H_p its heat at its own rates (averaged over the travels), H0_p at the base rate, F_p its fall
    two laps on. pi_p = F_p / H_p; pi_F = sum pi_p H0_p / sum H0_p over every part and the old entries (the floor's own share of the field);
    o_p the octave nearest log2(pi_p / pi_F) (octave_of), held at 0 or above and at most rate_bits - 1, and 0 where pi_p is 0 or less, its
    heat is zero, or pi_F is not above 0. Returns (pi, pi_F, octaves) with pi and octaves by part (OLD excluded from octaves)."""
    from fractions import Fraction
    pi = {p: (fall[p] / heat[p] if heat[p] > 0 else None) for p in heat}
    num = sum((pi[p] * heat_base[p] for p in heat if pi[p] is not None), Fraction(0))
    den = sum((heat_base[p] for p in heat if pi[p] is not None), Fraction(0))
    pi_f = num / den if den > 0 else Fraction(0)
    octaves = {}
    for p in heat:
        if p == OLD:
            continue
        if pi[p] is None or pi[p] <= 0 or pi_f <= 0:
            octaves[p] = 0
            continue
        octaves[p] = min(max(octave_of(pi[p] / pi_f), 0), rate_bits - 1)
    return pi, pi_f, octaves


def rational_learner(path):
    """A saved learner read for the law's prices in rationals: (lines, d, rate_bits, theta, s, parts), s each entry's floor root of its second
    moment (the deposit's own root, within one unit of the ruler's float root), parts the expanded octaves line or None."""
    from math import isqrt
    lines, d, rate, theta = load(path)
    second = [int(x) for x in lines[4].split(" ")]
    assert len(second) == len(theta), "a learner's text with its moments' lines"
    s = [isqrt(v) if v > 0 else 0 for v in second]
    return lines, d, rate, theta, s, parts_line(lines, d)


def polar(paths, state, out, sections=None, sites=None):
    """[definition; theory, November 11 21:15, G86] **A part's rate follows its polarization.** From the means of four consecutive laps
    A, B, C, D (in order) and for each founded part p, its heat H_p and its fall two laps on F_p, each at the part's own rates as
    tools/state_travel.py weighed prices them: an entry's heat over a travel is 2^(-rate - 32) s / (4 sites/sections) at the rates of the
    state the travel ends in, averaged over the three travels (polar_map.py's mean), its base heat the same at the base rate; its fall two
    laps on s_B d_AB d_CD 2^(rate - 32 - 2 grain) / sites, s_B and the rate the state between the first two travels'. pi_p = F_p / H_p, and
    the octaves by polar_octaves, decided in rationals of the means' integers (s the floor root of each second moment). STATE (the
    lap's end state the next lap trains from) is written to OUT with the new octaves on the parts it writes, every other line as it stands;
    one FIELD_PART_POLAR line a part: entries, heat, base heat, fall, pi (in the ruler's units, millionths of a bit a site, where SECTIONS and
    SITES are given; they only set the printed unit), the old octave and the new. Why (atlas deposition.lap-cosine-drift-over-noise and
    deposition.block-polarization): a part's lap fall is greatest at a rate of its drift's share over its noise, and pi_p over the field's
    pi_F is that share against the floor's, so its rate stands log2(pi_p / pi_F) octaves above the floor's."""
    from fractions import Fraction
    import state_travel
    lines, d, rate, theta_t, _, held = rational_learner(state)
    assert held is not None, "a state with no founded parts' rates (open sets them)"
    contacts_before, old_octaves = held
    means = [rational_learner(pth) for pth in paths]
    assert all(m[1] == d and len(m[3]) == len(theta_t) for m in means), "four means of the state's declaration"
    fam, total = state_travel.layout(d)
    grain = [0] * total
    for _, at, shape, g in fam:
        n = 1
        for x in shape:
            n *= x
        for i in range(at, at + n):
            grain[i] = g
    parts = founded_parts(d, contacts_before)
    keys = sorted(set(parts))

    def rates_of(m):
        r, oc = m[2], (m[5][1] if m[5] is not None else [0] * PARTS)
        return [max(r - (oc[p] if p != OLD else 0), 1) for p in parts]

    rates = [rates_of(m) for m in means]
    heat = {p: Fraction(0) for p in keys}
    heat_base = {p: Fraction(0) for p in keys}
    for k in range(3):
        nxt, r = means[k + 1], rates[k + 1]
        big = nxt[2]
        h = {p: 0 for p in keys}
        h0 = {p: 0 for p in keys}
        for i, p in enumerate(parts):
            si = nxt[4][i]
            if si:
                h[p] += si << (big - r[i])
                h0[p] += si
        for p in keys:
            heat[p] += Fraction(h[p], 2 ** (big + 32))
            heat_base[p] += Fraction(h0[p], 2 ** (big + 32))
    A, B, C, D = (m[3] for m in means)
    sB, rB = means[1][4], rates[1]
    f = {p: 0 for p in keys}
    for i, p in enumerate(parts):
        prod = sB[i] * (B[i] - A[i]) * (D[i] - C[i])
        if prod:
            f[p] += prod << (rB[i] + 48 - 2 * grain[i])
    unit_h = Fraction(sections * 10**6, 4 * sites) if sections and sites else Fraction(1)
    unit_f = Fraction(10**6, sites) if sections and sites else Fraction(1)
    heat = {p: heat[p] / 3 * unit_h for p in keys}
    heat_base = {p: heat_base[p] / 3 * unit_h for p in keys}
    fall = {p: Fraction(f[p], 2**80) * unit_f for p in keys}
    pi, pi_f, octaves = polar_octaves(heat, heat_base, fall, rate)
    show = lambda q: f"{float(q):.6g}" if q is not None else "-"
    for p in written(d):
        n = parts.count(p)
        new = octaves.get(p, 0)
        print(f"FIELD_PART_POLAR part={PART_NAMES[p]} entries={n} heat={show(heat.get(p, Fraction(0)))} heat_base={show(heat_base.get(p, Fraction(0)))} fall2={show(fall.get(p, Fraction(0)))} pi={show(pi.get(p))} octave_was={old_octaves[p]} octave={new}")
    print(f"FIELD_PART_POLAR_FIELD pi_F={show(pi_f)} old_entries={parts.count(OLD)} heat_old={show(heat.get(OLD, Fraction(0)))} fall2_old={show(fall.get(OLD, Fraction(0)))} rate_bits={rate} units={'millionths of a bit a site' if sections and sites else 'the means integers (no SECTIONS and SITES given)'}")
    new_octaves = list(old_octaves)
    for p in written(d):
        new_octaves[p] = octaves.get(p, 0)
    write(lines, d, contacts_before, new_octaves, out)


def fixed(num, den):
    """floor of num / den on 2^-GRAIN (den > 0)."""
    return (num << GRAIN) // den


def trend(paths, out):
    """[theory, November 11 03:54] The trend rule from four saved states OLDEST, OLDER, OLD, NOW of one line, each carrying the octaves
    its lap ran at (its `parts` line). Displacements da = OLDER - OLDEST (octave ka), db = OLD - OLDER (kb), dc = NOW - OLD (k, the present
    octave). c' = cos(da, db), c = cos(db, dc): with the earlier lap of a pair at rate eta, c = c_s - eta Hbar, so where ka != kb the slope
    h0 = (c' - c) / (2^kb - 2^ka), kept if positive, else 0. At the present octave: c^ = c + h0 (2^kb - 2^k), h = h0 2^k. Faster iff
    c^ > h/2 + eps, slower iff c^ < -h/4 - eps (never under octave 0), else rest, with eps^2 = sum_i db_i^2 dc_i^2 / (|db|^2 |dc|^2); one
    octave a lap at most, never past rate - 1. Every term is an integer on 2^-GRAIN."""
    states = [load(p) for p in paths]
    (_, d0, _, s0), (l1, d1, _, s1), (l2, d2, _, s2), (lines, d3, rate, s3) = states
    assert d0 == d1 == d2 == d3 and len(s0) == len(s1) == len(s2) == len(s3), "four states of one declaration"
    held = [parts_line(x[0], x[1]) for x in states[1:]]
    assert all(h is not None for h in held), "OLDER, OLD and NOW each carry the octaves their lap ran at"
    contacts_before = held[2][0]
    ka, kb, kn = held[0][1], held[1][1], held[2][1]
    parts = founded_parts(d3, contacts_before)
    acc = [[0] * 6 for _ in range(PARTS)]  # dot(da,db), |da|^2, |db|^2, dot(db,dc), |dc|^2, sum db^2 dc^2
    for i, p in enumerate(parts):
        if p == OLD:
            continue
        a, b, c = s1[i] - s0[i], s2[i] - s1[i], s3[i] - s2[i]
        q = acc[p]
        q[0] += a * b; q[1] += a * a; q[2] += b * b; q[3] += b * c; q[4] += c * c; q[5] += b * b * c * c
    one = 1 << GRAIN
    nxt = list(kn)
    for p in written(d3):
        name = PART_NAMES[p]
        dab, naa, nbb, dbc, ncc, s4 = acc[p]
        k = kn[p]
        if naa == 0 or nbb == 0 or ncc == 0:
            nxt[p] = max(k - 1, 0)
            print(f"FIELD_PART_RATE part={name} rule=trend c=- rate_octaves={nxt[p]} was={k} move={'slower' if nxt[p] < k else 'hold'} (a lap did not move it)")
            continue
        c1 = fixed(dab, isqrt(naa * nbb) or 1)   # c' on 2^-GRAIN
        c0 = fixed(dbc, isqrt(nbb * ncc) or 1)   # c
        eps = isqrt((s4 << (2 * GRAIN)) // (nbb * ncc))
        span = (1 << kb[p]) - (1 << ka[p])
        h0 = (c1 - c0) // span if span != 0 else 0
        if h0 < 0 or (span != 0 and (c1 - c0) * span < 0):
            h0 = 0
        chat = c0 + h0 * ((1 << kb[p]) - (1 << k))
        h = h0 * (1 << k)
        if 2 * chat > h + 2 * eps:
            k2 = min(k + 1, rate - 1)
        elif 4 * chat < -h - 4 * eps:
            k2 = max(k - 1, 0)
        else:
            k2 = k
        nxt[p] = k2
        r = lambda v: (lambda q: f"{'-' if v < 0 else ''}{q // 1_000_000}.{q % 1_000_000:06d}")(abs(v) * 1_000_000 >> GRAIN)
        move = "faster" if k2 > k else "slower" if k2 < k else "rest"
        print(f"FIELD_PART_RATE part={name} rule=trend c_prev={r(c1)} c={r(c0)} ka={ka[p]} kb={kb[p]} k={k} h0={r(h0)} c_hat={r(chat)} h={r(h)} eps={r(eps)} rate_octaves={k2} was={k} move={move} rate_bits={rate - k2}")
    write(lines, d3, contacts_before, nxt, out)


if __name__ == "__main__":
    main()
