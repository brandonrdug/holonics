#!/usr/bin/env -S python3 -I
"""part_rates.py: the founded parts' deposit rates, moved between laps from saved states (host arithmetic: no card, no model).

  part_rates.py open STATE CONTACTS_BEFORE OCTAVES OUT
  part_rates.py update OLDER OLD NOW OUT
  part_rates.py means OLDER OLD NOW STATE OUT    (theory, November 11: the same rule read on lap means; see below)
  part_rates.py trend OLDEST OLDER OLD NOW OUT   (theory, November 11 03:54: the slope-corrected rule; see trend())
  part_rates.py base STATE RATE_BITS OUT         (theory, November 11: the learner's own rate word; see below)
  part_rates.py polar MEAN_A MEAN_B MEAN_C MEAN_D STATE OUT [SECTIONS SITES]   (theory, November 11 21:15, G86: a part's rate follows its
                                                 polarization; see polar())
  part_rates.py blocks MEAN_A MEAN_B MEAN_C MEAN_D STATE OUT [SECTIONS SITES]  (theory, November 12 00:20, G86's branch 1: every block a
                                                 part of its own, each entry's own rate; see blocks())
  part_rates.py own STATE OUT                    (theory, November 12: the state with each entry's rate written as its own; see below)

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

Each entry's own rate (theory, November 12 00:20, the Einstein record's U2): a state may carry a trailing `rates r0 .. r(n-1)` line after its
parts line, one count an entry (holonics::hnn::tower::field::FieldLearner::own_rates), and where it stands it is every entry's rate: the
parts' octaves and the base word then govern none (the parts line is kept for its contacts count). `blocks` writes it; the octave verbs
(open, update, means, trend, polar) and `base` refuse a state that carries it, since an octave they moved would move no entry. Every reader
here and in tools/state_travel.py takes an entry's rate from it where it stands. `own` writes STATE with the line set to the rates its
parts and base word give (FieldLearner::entry_rates), every other line as it stands: the same rates carried the new way, a state a build
of the line trains from to show that the line changes no bit where the rates are the parts'.
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


WIDEST_RATE = 127  # an entry's rate is under the step's carrier: the deposit shifts an i128 (holonics::hnn::tower::deposit_step)


def own_line(lines, total=None):
    """A state's `rates` line, each entry's own deposit rate in bits (theory, November 12; FieldLearner::own_rates), as a list; None
    without one."""
    for l in lines:
        if l.startswith("rates "):
            v = [int(x) for x in l.split(" ")[1:]]
            assert total is None or len(v) == total, "a learner's own rates, one an entry"
            assert all(0 < r <= WIDEST_RATE for r in v), "an entry's own rate under one bit or past the step's carrier"
            return v
    return None


def learner_rates(d, rate, held, own, total):
    """Each entry's deposit rate in bits (FieldLearner::entry_rates): its own where the state carries the `rates` line; otherwise the
    base word, less its founded part's octaves (held, a parts line as parts_line reads it, or None), never under one bit."""
    if own is not None:
        assert len(own) == total, "a learner's own rates, one an entry"
        return list(own)
    if held is None:
        return [rate] * total
    parts = founded_parts(d, held[0])
    assert len(parts) == total
    return [max(rate - (held[1][p] if p != OLD else 0), 1) for p in parts]


def write_rates(lines, rates, out):
    """A state's lines with its `rates` line set to RATES (one count an entry), after its parts line (FieldLearner::from_text reads the
    line where the parts line ends), every other line as it stands."""
    kept = [l for l in lines if not l.startswith("rates ")]
    while kept and kept[-1] == "":
        kept.pop()
    assert not any(l.startswith("parts ") for l in kept) or kept[-1].startswith("parts "), "a learner's text whose parts line is its last"
    assert all(0 < r <= WIDEST_RATE for r in rates), "an entry's own rate under one bit or past the step's carrier"
    kept.append("rates " + " ".join(str(r) for r in rates))
    with open(out, "x") as f:
        f.write("\n".join(kept) + "\n")


def census(rates):
    """The entries at each rate, fastest first, as the trainer's FIELD_OWN_RATES prints them."""
    at = {}
    for r in rates:
        at[r] = at.get(r, 0) + 1
    return " ".join(f"{r}:{at[r]}" for r in sorted(at))


def write(lines, d, contacts_before, octaves, out):
    assert own_line(lines) is None, "a state whose entries carry their own rates (its rates line): a part's octave moves none of them"
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
    elif len(args) in (7, 9) and args[0] == "blocks":
        blocks(args[1:5], args[5], args[6], *(int(x) for x in args[7:9]))
    elif len(args) == 3 and args[0] == "own":
        lines, d, rate, theta = load(args[1])
        assert own_line(lines) is None, "a state that carries its own rates already"
        rates = learner_rates(d, rate, parts_line(lines, d), None, len(theta))
        print(f"FIELD_OWN_RATES entries={len(rates)} rate_bits={rate} at {census(rates)}")
        write_rates(lines, rates, args[2])
    elif len(args) == 4 and args[0] == "base":
        lines, d, rate, _ = load(args[1])
        assert own_line(lines) is None, "a state whose entries carry their own rates (its rates line): the base word moves none of them"
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
    """A saved learner read for the law's prices in rationals: (lines, d, rate_bits, theta, s, parts, own), s each entry's floor root of its
    second moment (the deposit's own root, within one unit of the ruler's float root), parts the expanded octaves line or None, own its
    rates line (each entry's own rate, theory, November 12) or None."""
    from math import isqrt
    lines, d, rate, theta = load(path)
    second = [int(x) for x in lines[4].split(" ")]
    assert len(second) == len(theta), "a learner's text with its moments' lines"
    s = [isqrt(v) if v > 0 else 0 for v in second]
    return lines, d, rate, theta, s, parts_line(lines, d), own_line(lines, len(theta))


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
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import state_travel
    lines, d, rate, theta_t, _, held, own_t = rational_learner(state)
    assert held is not None, "a state with no founded parts' rates (open sets them)"
    assert own_t is None, "a state whose entries carry their own rates (its rates line): a part's octave moves none of them"
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
        if m[6] is not None:  # a mean whose entries carried their own rates (theory, November 12)
            return list(m[6])
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


def block_octave(pi, pi_f, present, rate_bits):
    """[definition; theory, November 12 00:20] A block's octave under the block law, in rationals (Fraction), with no float; None where it
    holds. pi the block's polarization at its own rates (None where it holds no heat), pi_f the floor's (None where there is no floor),
    present its octaves in STATE (one, or the several a parts line gave a block that mixes parts). The octave nearest log2(pi / pi_f)
    (octave_of), signed: under 0 where its polarization stands under the floor's, a rate above the base word. Where pi is 0 or under, one
    octave under the coolest of its present ones. Bounded by an entry's rate of one bit (rate_bits - 1) and of WIDEST_RATE."""
    if pi is None or pi_f is None or pi_f <= 0:
        return None
    lo, hi = rate_bits - WIDEST_RATE, rate_bits - 1
    o = min(present) - 1 if pi <= 0 else octave_of(pi / pi_f)
    return min(max(o, lo), hi)


def blocks(paths, state, out, sections=None, sites=None):
    """[definition; theory, November 12 00:20: G86's rule, branch 1, and the Einstein record's U2] **Every block a part of its own.** The
    blocks are tools/state_travel.py's scale_blocks (each family by lane and by new or old contacts; with carry circles the turn rows and
    the leak rows apart, and their biases apart), the partition G86's polarization was read on and every entry in one of them. From the
    means of four consecutive laps A, B, C, D (in order) and for each block b: its heat H_b and its fall two laps on F_b at its entries'
    own rates, priced as polar() prices a part's (the heat averaged over the three travels at the rates of the state each ends in, the
    fall at the rates of B), pi_b = F_b / H_b, in rationals of the means' integers.
    - A block moves only where its window stands at one rate: every entry's rate the same in the four means as in STATE (the lap's end
      state the next lap trains from). Reason: G86 (c) missed because its window straddled a change of rates (one raised travel at g2,
      two at g3), and a fall two laps on read across a change mixes the travel of two rates (the guess file's G86 score). So a block
      that moves holds through its next four laps.
    - The floor pi_F = sum F_b / sum H_b over the blocks whose every entry stood at the base word in all four means.
    - A block in its window takes block_octave: the octave nearest log2(pi_b / pi_F), signed, so a block whose polarization stands under
      the floor's steps under the base word. Reason (U2): a part whose travel returns two laps on buys nothing and holds rent, so its rate
      belongs under the floor, and pi_b / pi_F is its drift's share over its noise against the floor's (atlas
      deposition.block-polarization). Where F_b is 0 or under, one octave under its present. Every entry of the block takes the block's
      rate, so a block that mixed parts (the first lane's read rows under a parts line) becomes one.
    - A block without heat holds, and every block holds where no block stood at the floor.
    STATE is written to OUT with its rates line (one count an entry, after its parts line, which is kept for its contacts count and no
    longer governs; FieldLearner::own_rates), every other line as it stands. One FIELD_BLOCK_RATE line a block (its entries, the open ones
    in D, heat, base heat, fall, pi in the ruler's units, millionths of a bit a site, where SECTIONS and SITES are given; whether its
    window stands at one rate; its octave in STATE and the new), FIELD_BLOCK_FLOOR, and FIELD_BLOCK_RATES, the entries at each rate.
    Owed, each with its guess before it acts (agent-inferred): on a line with a founding inside the window, the floor leaves out the blocks
    that charge, whose fall is their charging; and at a moved block's fourth lap at its new rate, the step between two windows at two
    octaves, where a raise that paid (its marginal dF/dH above pi_F) takes one more octave and one that did not steps back."""
    from fractions import Fraction
    import numpy as np
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import state_travel
    lines, d, rate, theta_t, _, held, own_t = rational_learner(state)
    assert held is not None, "a state with its count of contacts before the growth (its parts line; open sets it)"
    contacts_before = held[0]
    total = len(theta_t)
    assert len(paths) == 4, "four means"
    means = [rational_learner(pth) for pth in paths]
    assert all(m[1] == d and len(m[3]) == total for m in means), "four means of the state's declaration"
    assert all(m[2] == rate for m in means), "four means at the state's base word (a move of the base word is a window of two rates)"
    assert all(m[5] is None or m[5][0] == contacts_before for m in means), "four means of the state's contacts"
    fam, length = state_travel.layout(d)
    assert length == total, "the material's length"
    at_of = {name: at for name, at, _, _ in fam}
    grain = [0] * total
    for _, at, shape, g in fam:
        n = 1
        for x in shape:
            n *= x
        for i in range(at, at + n):
            grain[i] = g
    blk, seen = [], [0] * total
    for block, lane, contacts, _, family, mask in state_travel.scale_blocks(d, contacts_before):
        idx = [at_of[family] + int(j) for j in np.flatnonzero(mask.ravel())]
        for i in idx:
            seen[i] += 1
        blk.append((block, lane, contacts, idx))
    assert all(x == 1 for x in seen), "the blocks hold every entry once"
    now = learner_rates(d, rate, held, own_t, total)
    rates = [learner_rates(d, rate, m[5], m[6], total) for m in means]
    big = max(max(r) for r in rates)
    unit_h = Fraction(sections * 10**6, 4 * sites) if sections and sites else Fraction(1)
    unit_f = Fraction(10**6, sites) if sections and sites else Fraction(1)
    A, B, C, D = (m[3] for m in means)
    sB, rB = means[1][4], rates[1]
    rows = []
    for block, lane, contacts, idx in blk:
        h = sum(means[k + 1][4][i] << (big - rates[k + 1][i]) for k in range(3) for i in idx)
        h0 = sum(means[k + 1][4][i] for k in range(3) for i in idx)
        f = sum((sB[i] * (B[i] - A[i]) * (D[i] - C[i])) << (rB[i] + 48 - 2 * grain[i]) for i in idx)
        heat = Fraction(h, 2 ** (big + 32)) / 3 * unit_h
        rows.append({
            "block": block, "lane": lane, "contacts": contacts, "idx": idx,
            "heat": heat, "heat_base": Fraction(h0, 2 ** (rate + 32)) / 3 * unit_h, "fall": Fraction(f, 2**80) * unit_f,
            "open": sum(1 for i in idx if means[3][4][i] > 0),
            "one": all(r[i] == now[i] for r in rates for i in idx),
            "floor": all(r[i] == rate for r in rates for i in idx),
            "present": sorted({rate - now[i] for i in idx}),
        })
    floor = [r for r in rows if r["floor"] and r["heat"] > 0]
    floor_heat = sum((r["heat"] for r in floor), Fraction(0))
    floor_fall = sum((r["fall"] for r in floor), Fraction(0))
    pi_f = floor_fall / floor_heat if floor_heat > 0 else None
    new = list(now)
    show = lambda q: f"{float(q):.6g}" if q is not None else "-"
    for r in rows:
        pi = r["fall"] / r["heat"] if r["heat"] > 0 else None
        o = block_octave(pi, pi_f, r["present"], rate) if r["one"] else None
        was = "..".join(str(k) for k in (r["present"] if len(r["present"]) == 1 else (r["present"][0], r["present"][-1])))
        if o is None:
            move, octave = ("hold" if r["one"] else "window"), was
        else:
            for i in r["idx"]:
                new[i] = rate - o
            octave = str(o)
            move = "hold" if r["present"] == [o] else ("raise" if o > r["present"][-1] else "cool" if o < r["present"][0] else "join")
        print(f"FIELD_BLOCK_RATE block={r['block']} lane={r['lane']} contacts={r['contacts']} entries={len(r['idx'])} open={r['open']} heat={show(r['heat'])} heat_base={show(r['heat_base'])} fall2={show(r['fall'])} pi={show(pi)} window={'one' if r['one'] else 'two'} octave_was={was} octave={octave} move={move} rate_bits={rate - int(octave) if o is not None or len(r['present']) == 1 else '-'}")
    print(f"FIELD_BLOCK_FLOOR pi_F={show(pi_f)} blocks={len(floor)} entries={sum(len(r['idx']) for r in floor)} heat={show(floor_heat)} fall2={show(floor_fall)} rate_bits={rate} units={'millionths of a bit a site' if sections and sites else 'the means integers (no SECTIONS and SITES given)'}")
    print(f"FIELD_BLOCK_RATES entries={total} rate_bits={rate} at {census(new)}")
    write_rates(lines, new, out)


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
