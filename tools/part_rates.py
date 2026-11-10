#!/usr/bin/env python3 -I
"""part_rates.py: the founded parts' deposit rates, moved between laps from saved states (host arithmetic: no card, no model).

  part_rates.py open STATE CONTACTS_BEFORE OCTAVES OUT
  part_rates.py update OLDER OLD NOW OUT

The learner's text carries each founded part's octaves in a trailing `parts CONTACTS_BEFORE k0 .. k14` line (holonics::hnn::tower::field::
RateParts); the trainer steps part p at 2^-(rate - k_p). `open` writes STATE with the octaves OCTAVES (fifteen counts, comma separated, in
PART_NAMES order). `update` reads three saved states of one line and, for each part, the cosine c between its displacements OLD - OLDER and
NOW - OLD over the entries it holds (exact integers): c > 1/2 one octave faster, c < 1/2 one slower, never under the old rate (octave 0) nor
past rate - 1; c = 1/2 rests. It writes NOW with the moved octaves to OUT and prints FIELD_PART_RATE for every part. The parts are
Field::founded_parts' (checked against it by the ignored test founded_parts_and_their_cosines_on_saved_states). Numbers only.
"""
import sys
from math import isqrt

PART_NAMES = ["w_new", "a_new", "b_new", "enc_lane", "before_lane", "after_lane", "q_lane", "v_lane", "probe_lane", "out_lane", "moment_face_lane", "read_lane", "face_biases_lane", "a_lane", "b_lane"]
PARTS = len(PART_NAMES)
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
    return parts


def load(path):
    lines = open(path).read().split("\n")
    words = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes"]
    d = {k: int(w) for k, w in zip(names, words[1:11])}
    rate = int(lines[0].split(" ")[1])
    theta = [int(x) for x in lines[2].split(" ")]
    return lines, d, rate, theta


def parts_line(lines):
    for l in lines:
        if l.startswith("parts "):
            v = [int(x) for x in l.split(" ")[1:]]
            assert len(v) == 1 + PARTS
            return v[0], v[1:]
    return None


def write(lines, contacts_before, octaves, out):
    kept = [l for l in lines if not l.startswith("parts ")]
    while kept and kept[-1] == "":
        kept.pop()
    kept.append("parts " + " ".join(str(x) for x in [contacts_before] + octaves))
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
        assert len(octaves) == PARTS and all(0 <= k < rate for k in octaves), "fifteen octave counts each under the rate's bits"
        assert 0 < contacts_before <= d["contacts"] and contacts_before % 4 == 0
        parts = founded_parts(d, contacts_before)
        for p, name in enumerate(PART_NAMES):
            print(f"FIELD_PART_RATE part={name} entries={parts.count(p)} c=- rate_octaves={octaves[p]} rate_bits={rate - octaves[p]}")
        write(lines, contacts_before, octaves, args[4])
    elif len(args) == 5 and args[0] == "update":
        (_, da, ra, older), (_, db, rb, old), (lines, dc, rate, now) = load(args[1]), load(args[2]), load(args[3])
        assert da == db == dc and len(older) == len(old) == len(now), "three states of one declaration"
        held = parts_line(lines)
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
        nxt = []
        for p, name in enumerate(PART_NAMES):
            k = octaves[p]
            if first[p] == 0 or second[p] == 0 or dot[p] <= 0:
                side = -1
            else:
                lhs, rhs = 4 * dot[p] * dot[p], first[p] * second[p]
                side = (lhs > rhs) - (lhs < rhs)
            k2 = min(k + 1, rate - 1) if side > 0 else (max(k - 1, 0) if side < 0 else k)
            nxt.append(k2)
            root = isqrt(first[p] * second[p])
            c = micro(dot[p], root) if root > 0 else 0
            move = "faster" if k2 > k else "slower" if k2 < k else "hold"
            print(f"FIELD_PART_RATE part={name} entries={entries[p]} c={'-' if c < 0 else ''}{abs(c) // 1_000_000}.{abs(c) % 1_000_000:06d} rate_octaves={k2} was={k} move={move} rate_bits={rate - k2}")
        write(lines, contacts_before, nxt, args[4])
    else:
        sys.exit(__doc__)


main()
