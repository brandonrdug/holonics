#!/usr/bin/env -S python3 -I
"""Controls of part_rates.py's rate rule on drawn states (host arithmetic; no saved state of a line is read).

Three small states of one declaration are written with a planted travel of three of the second lane's parts:
  steady      the key chart's lane columns move by one vector on both laps: cosine 1, one octave faster;
  reversing   the value chart's lane columns move by one vector and back: cosine -1, one octave slower;
  at the half the probe chart's lane columns move by (2, 0, 0, 0) and then (1, 1, 1, 1) in every four entries: cosine 1/2, the part rests;
  unmoved     every other part: no travel, one octave slower, never under the old rate.
`update` prints those moves and writes the last state with the moved octaves.

`means`, the same rule read on three other materials with the octaves moved in a named state:
  the same three   with the three states as the materials and the last as the state it writes what `update` writes, byte for byte;
  another state    the written file holds the named state's material and lines and that state's octaves, moved by the materials' cosines;
  the spread       lap ends that carry a draw of a standing spread (a steady travel of 2 an entry a lap, end draws of 3 that reverse sign
                   at each lap end) read cosine -1 between lap ends, so `update` slows the part; the laps' means, which shed the draw,
                   read cosine 1, so `means` raises it, in the end state the next lap trains from;
  refusals         a state of another declaration, and a file that stands, are refused.

`base`, the learner's own rate word: the written file is the state's with the second word of its first line changed and nothing else
(every other word, line and the material byte for byte, with or without a parts line); a rate at or under a part's octave, a rate of
no bits and a file that stands are refused.
"""
import io
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import part_rates  # noqa: E402

D = {"alphabet": 5, "width": 16, "heads": 4, "modes": 2, "still": 2, "contacts": 16, "ticks": 4, "frames": 4, "reach": 16, "lanes": 2, "carry": 0}
OLD_F = 8
KEYS = ("alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes")


def write(path, theta, octaves, d=D, extra=None):
    c = d.get("carry", 0)
    words = (["hnn-field-v14t"] if c else ["hnn-field-v14"]) + [str(d[k]) for k in KEYS] + ["0"] + ([str(c)] if c else [])
    with open(path, "w") as f:
        f.write("hnn-field-learner-v3 12 0 0 -\n" + " ".join(words) + "\n" + " ".join(str(int(x)) for x in theta) + "\n")
        if extra is not None:
            f.write(extra + "\n")
        # A full list of PARTS octaves is written in the line's order for d (part_rates.written); any other list as it stands (an older line).
        line = [octaves[p] for p in part_rates.written(d)] if len(octaves) == part_rates.PARTS else octaves
        f.write("parts " + " ".join(str(k) for k in [OLD_F] + line) + "\n")


def run(*args):
    out = io.StringIO()
    old = sys.argv
    sys.argv = ["part_rates.py"] + list(args)
    try:
        with redirect_stdout(out):
            part_rates.main()
    finally:
        sys.argv = old
    lines = [l for l in out.getvalue().split("\n") if l.startswith("FIELD_PART_RATE ")]
    return {f["part"]: f for f in ({k: v for k, v in (w.split("=", 1) for w in l.split(" ")[1:])} for l in lines)}


def draws(n, seed):
    x, out = seed, []
    for _ in range(n):
        x = (x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        out.append((x >> 40) % 2001 - 1000)
    return out


def main():
    _, total = part_rates.layout(D)
    parts = part_rates.founded_parts(D, OLD_F)
    assert len(parts) == total
    where = lambda name: [i for i, p in enumerate(parts) if p == part_rates.PART_NAMES.index(name)]
    q, v, pr = where("q_lane"), where("v_lane"), where("probe_lane")
    assert q and v and len(pr) % 4 == 0 and pr
    base = draws(total, 7)
    step = draws(total, 11)
    octaves = [0] * part_rates.PARTS
    octaves[part_rates.PART_NAMES.index("q_lane")] = 0
    octaves[part_rates.PART_NAMES.index("v_lane")] = 2
    octaves[part_rates.PART_NAMES.index("probe_lane")] = 1
    octaves[part_rates.PART_NAMES.index("enc_lane")] = 3
    s0, s1, s2 = list(base), list(base), list(base)
    for i in q:
        s1[i] += step[i]
        s2[i] += 2 * step[i]
    for i in v:
        s1[i] += step[i]
    for n, i in enumerate(pr):
        s1[i] += 2 if n % 4 == 0 else 0
        s2[i] += (2 if n % 4 == 0 else 0) + 1
    with tempfile.TemporaryDirectory() as t:
        p = lambda name: os.path.join(t, name)
        write(p("s0"), s0, octaves)
        write(p("s1"), s1, octaves)
        write(p("s2"), s2, octaves, extra="a line the tool keeps")
        got = run("update", p("s0"), p("s1"), p("s2"), p("u"))
        assert got["q_lane"]["c"] == "1.000000" and got["q_lane"]["move"] == "faster" and got["q_lane"]["rate_octaves"] == "1", got["q_lane"]
        assert got["v_lane"]["c"] == "-1.000000" and got["v_lane"]["move"] == "slower" and got["v_lane"]["rate_octaves"] == "1", got["v_lane"]
        assert got["probe_lane"]["c"] == "0.500000" and got["probe_lane"]["move"] == "hold" and got["probe_lane"]["rate_octaves"] == "1", got["probe_lane"]
        assert got["enc_lane"]["move"] == "slower" and got["enc_lane"]["rate_octaves"] == "2", got["enc_lane"]
        assert got["w_new"]["move"] == "hold" and got["w_new"]["rate_octaves"] == "0", got["w_new"]
        moved = list(octaves)
        for name, k in (("q_lane", 1), ("v_lane", 1), ("probe_lane", 1), ("enc_lane", 2)):
            moved[part_rates.PART_NAMES.index(name)] = k
        text = open(p("u")).read().split("\n")
        assert text[2] == " ".join(str(x) for x in s2) and text[3] == "a line the tool keeps"
        assert text[-2] == "parts " + " ".join(str(k) for k in [OLD_F] + [moved[p] for p in part_rates.written(D)]) and text[-1] == ""
        print("part_rates update: the planted moves and the written state hold")

        # The same three materials, the last as the state: what update writes.
        again = run("means", p("s0"), p("s1"), p("s2"), p("s2"), p("m"))
        assert again == got and open(p("m")).read() == open(p("u")).read()
        # Another state: its material, its lines and its octaves, moved by the materials' cosines.
        other, other_octaves = draws(total, 23), list(octaves)
        other_octaves[part_rates.PART_NAMES.index("q_lane")] = 4
        other_octaves[part_rates.PART_NAMES.index("v_lane")] = 0
        write(p("e"), other, other_octaves, extra="the end state's own line")
        got2 = run("means", p("s0"), p("s1"), p("s2"), p("e"), p("m2"))
        assert got2["q_lane"]["was"] == "4" and got2["q_lane"]["rate_octaves"] == "5" and got2["v_lane"]["was"] == "0" and got2["v_lane"]["rate_octaves"] == "0"
        text = open(p("m2")).read().split("\n")
        assert text[2] == " ".join(str(x) for x in other) and text[3] == "the end state's own line"
        assert text[-2].split(" ")[1 + 1 + part_rates.PART_NAMES.index("q_lane")] == "5"
        print("part_rates means: the same three write what update writes; another state keeps its material and moves its own octaves")

        # The spread: lap ends carry a draw that reverses; the laps' means do not.
        e0, e1, e2, m0, m1, m2 = (list(base) for _ in range(6))
        for i in q:
            for k, (e, m) in enumerate(((e0, m0), (e1, m1), (e2, m2))):
                m[i] += 2 * k
                e[i] += 2 * k + (3 if k % 2 == 0 else -3)
        raised = list(octaves)
        raised[part_rates.PART_NAMES.index("q_lane")] = 1
        for name, th in (("e0", e0), ("e1", e1), ("e2", e2), ("m0", m0), ("m1", m1), ("m2", m2)):
            write(p(name), th, raised)
        ends = run("update", p("e0"), p("e1"), p("e2"), p("ue"))
        means = run("means", p("m0"), p("m1"), p("m2"), p("e2"), p("um"))
        # Between lap ends the displacements are 2 - 6 and 2 + 6 an entry: cosine -1; between the means 2 and 2: cosine 1.
        assert ends["q_lane"]["c"] == "-1.000000" and ends["q_lane"]["move"] == "slower" and ends["q_lane"]["rate_octaves"] == "0", ends["q_lane"]
        assert means["q_lane"]["c"] == "1.000000" and means["q_lane"]["move"] == "faster" and means["q_lane"]["rate_octaves"] == "2", means["q_lane"]
        assert open(p("um")).read().split("\n")[2] == " ".join(str(x) for x in e2)
        print("part_rates means: a steady travel under a reversing draw reads at rest between lap ends and steady between lap means")

        # Refusals.
        d2 = dict(D, contacts=24)
        _, total2 = part_rates.layout(d2)
        write(p("x"), draws(total2, 5), octaves, d=d2)
        for args in (("means", p("s0"), p("s1"), p("s2"), p("x"), p("r1")), ("means", p("s0"), p("s1"), p("s2"), p("s2"), p("m"))):
            try:
                run(*args)
            except (AssertionError, FileExistsError):
                pass
            else:
                raise AssertionError(f"not refused: {args[0]} onto {os.path.basename(args[4])} writing {os.path.basename(args[5])}")
        assert not os.path.exists(p("r1"))
        print("part_rates means: a state of another declaration and a standing file are refused")

        # The base rate: the head line's rate word alone.
        run("base", p("s2"), "11", p("b"))
        was, now = open(p("s2")).read(), open(p("b")).read()
        assert was.startswith("hnn-field-learner-v3 12 0 0 -\n") and now == "hnn-field-learner-v3 11 0 0 -\n" + was.split("\n", 1)[1]
        bare = "\n".join(l for l in was.split("\n") if not l.startswith("parts "))
        with open(p("bare"), "w") as f:
            f.write(bare)
        run("base", p("bare"), "9", p("b9"))
        assert open(p("b9")).read() == "hnn-field-learner-v3 9 0 0 -\n" + bare.split("\n", 1)[1]
        # s2 carries an octave of 3 (enc_lane): a rate of 3 bits is refused, 4 is written; no bits and a standing file are refused.
        for args in (("base", p("s2"), "3", p("r2")), ("base", p("s2"), "0", p("r3")), ("base", p("s2"), "11", p("b"))):
            try:
                run(*args)
            except (AssertionError, FileExistsError):
                pass
            else:
                raise AssertionError(f"not refused: base at {args[2]} bits writing {os.path.basename(args[3])}")
        assert not os.path.exists(p("r2")) and not os.path.exists(p("r3"))
        run("base", p("s2"), "4", p("b4"))
        assert open(p("b4")).read().startswith("hnn-field-learner-v3 4 0 0 -\n")
        print("part_rates base: the rate word alone moves; a rate under a part's octave, no bits and a standing file are refused")

        # The carry circles (theory, November 11 17:25): two circles of eight complex contacts, their four parts over the new contacts' marks,
        # nineteen parts written; a sixteen-part line reads with the circles' parts at octave 0; the retired carry's head is refused.
        dc = dict(D, carry=2)
        fam, total_c = part_rates.layout(dc)
        assert total_c == total + 2 * 2 * 16 + 2 * 2 and fam["carry"] == total and fam["carry_bias"] == total + 2 * 2 * 16
        parts_c = part_rates.founded_parts(dc, OLD_F)
        count = lambda name: sum(1 for q in parts_c if q == part_rates.PART_NAMES.index(name))
        assert (count("carry"), count("w_carry"), count("a_carry"), count("b_carry")) == (4 * 16 + 4, 4 * 16, 4 * 16 + 4, 4 * 16 + 4)
        assert count("w_new") == 16 * (16 - OLD_F - 4), "the circles' columns are theirs, not the new contacts'"
        write(p("c0"), draws(total_c, 3), octaves[:part_rates.PLAIN_PARTS], d=dc)
        run("open", p("c0"), str(OLD_F), ",".join(str(k) for k in [0] * part_rates.PARTS), p("c1"))
        line = [l for l in open(p("c1")).read().split("\n") if l.startswith("parts ")][0]
        assert len(line.split(" ")) == 2 + part_rates.PARTS, line
        held = part_rates.parts_line(open(p("c0")).read().split("\n"), dc)
        assert held[1][part_rates.PLAIN_PARTS:] == [0] * 6, "a sixteen-part line reads the circles' and the letter rows' parts at octave 0"
        got_c = run("update", p("c0"), p("c0"), p("c0"), p("c2"))
        assert set(got_c) == set(part_rates.PART_NAMES), "a state with carry circles prints all nineteen"
        assert len([l for l in open(p("c2")).read().split("\n") if l.startswith("parts ")][0].split(" ")) == 2 + part_rates.PARTS
        with open(p("k"), "w") as f:
            f.write(open(p("s0")).read().replace("hnn-field-v14 ", "hnn-field-v14k ", 1).replace(" 0\n", " 0 1\n", 1))
        try:
            part_rates.load(p("k"))
        except AssertionError:
            pass
        else:
            raise AssertionError("the retired carry's head is not refused")
        print("part_rates carry: the circles' four parts, twenty-two written, sixteen read at octave 0, the retired head refused")

        # The first lane's letter rows (theory, November 11 21:15, G86): three parts of their own, the encodings' columns over the first lane;
        # a field without circles writes nineteen (sixteen and these three), with circles twenty-two; an older line reads them at octave 0.
        first = {n: sum(1 for q in parts if q == part_rates.PART_NAMES.index(n)) for n in ("enc_first", "before_first", "after_first")}
        assert first == {"enc_first": 6 * 8, "before_first": 6 * 8, "after_first": 6 * 8}, first
        assert part_rates.written(D) == list(range(16)) + [19, 20, 21] and part_rates.written(dc) == list(range(22))
        raised = [0] * part_rates.PARTS
        raised[part_rates.PART_NAMES.index("before_first")] = 3
        write(p("f0"), base, raised)
        assert len([l for l in open(p("f0")).read().split("\n") if l.startswith("parts ")][0].split(" ")) == 2 + 19
        assert part_rates.parts_line(open(p("f0")).read().split("\n"), D)[1] == raised, "nineteen parts read back by the line's order"
        assert part_rates.expand(D, [0] * 16)[19:] == [0, 0, 0] and part_rates.expand(dc, [0] * 19)[19:] == [0, 0, 0]
        got_f = run("update", p("f0"), p("f0"), p("f0"), p("f1"))
        assert set(got_f) == set(part_rates.PART_NAMES[p] for p in part_rates.written(D)), "a field without circles prints its nineteen"
        print("part_rates first: the letter rows' three parts, nineteen written without circles, older lines read at octave 0")
        polar_controls(p)
    print("part_rates: 9 lines, the controls hold")


def learner_text(path, theta, second, octaves, d=D, rate=12):
    """A learner's text with its moments' lines (first moments zero), for the law's controls."""
    c = d.get("carry", 0)
    words = (["hnn-field-v14t"] if c else ["hnn-field-v14"]) + [str(d[k]) for k in KEYS] + ["0"] + ([str(c)] if c else [])
    line = [octaves[p] for p in part_rates.written(d)]
    with open(path, "w") as f:
        f.write(f"hnn-field-learner-v3 {rate} 0 0 -\n" + " ".join(words) + "\n" + " ".join(str(int(x)) for x in theta) + "\n"
                + " ".join("0" for _ in theta) + "\n" + " ".join(str(int(x)) for x in second) + "\n" + "parts " + " ".join(str(k) for k in [OLD_F] + line) + "\n")


def polar_controls(p):
    """[theory, November 11 21:15, G86] The law: a part's rate follows its polarization, decided in rationals."""
    from fractions import Fraction as Fr
    OLD = part_rates.OLD
    # The decision alone: octaves known from the ratio, the edges on either side, a part with no fall, the clamps.
    # The old entries hold the field's pi_F at 1 to within 10^-11, so each part's ratio is its own pi: 4 is two octaves, 2^20 is clamped at
    # rate_bits - 1, no fall and a fall below zero are the floor.
    heat = {0: Fr(1), 3: Fr(1), 4: Fr(1, 10**6), 5: Fr(1), OLD: Fr(10**12)}
    fall = {0: Fr(4), 3: Fr(0), 4: Fr(2**20, 10**6), 5: Fr(-1), OLD: Fr(10**12)}
    pi, pi_f, octaves = part_rates.polar_octaves(heat, dict(heat), fall, 12)
    assert abs(pi_f - 1) < Fr(1, 10**11) and pi[0] == 4 and pi[4] == 2**20
    assert octaves == {0: 2, 3: 0, 4: 11, 5: 0}, octaves
    assert [part_rates.octave_of(Fr(x)) for x in ("1.41", "1.42", "2.82", "2.83", "0.70", "0.71")] == [0, 1, 1, 2, -1, 0], "the edges at 2^(o +- 1/2)"
    _, _, at_floor = part_rates.polar_octaves({0: Fr(1), OLD: Fr(1)}, {0: Fr(1), OLD: Fr(1)}, {0: Fr(-1), OLD: Fr(1)}, 12)
    assert at_floor == {0: 0}, "a part whose fall is below zero stays at the floor"
    # On four synthetic means: every entry's travel set so its fall two laps on is one unit (d = 2^(grain - 16)) gives every part the same
    # polarization, the fixed point (every octave 0); doubling one part's two travels makes its fall four times, two octaves above the floor.
    import state_travel
    fam, total = state_travel.layout(D)
    grain = [0] * total
    for _, at, shape, g in fam:
        n = 1
        for x in shape: n *= x
        for i in range(at, at + n): grain[i] = g
    parts = part_rates.founded_parts(D, OLD_F)
    second = [1 << 20] * total
    zero = [0] * part_rates.PARTS
    for name, scale_part, expect in (("flat", None, None), ("raised", part_rates.PART_NAMES.index("q_lane"), 2)):
        theta = [[0] * total for _ in range(4)]
        for i in range(total):
            unit = 1 << (grain[i] - 16)
            k = 2 if scale_part is not None and parts[i] == scale_part else 1
            theta[1][i] = k * unit
            theta[2][i] = k * unit
            theta[3][i] = 2 * k * unit
        paths = []
        for j in range(4):
            path = p(f"{name}_m{j}")
            learner_text(path, theta[j], second, zero)
            paths.append(path)
        out = io.StringIO()
        with redirect_stdout(out):
            part_rates.polar(paths, paths[3], p(f"{name}_out"))
        got = {f["part"]: int(f["octave"]) for f in ({k: v for k, v in (w.split("=", 1) for w in l.split(" ")[1:])} for l in out.getvalue().split("\n") if l.startswith("FIELD_PART_POLAR "))}
        if scale_part is None:
            assert all(o == 0 for o in got.values()), got
        else:
            assert got["q_lane"] == expect and all(o == 0 for n, o in got.items() if n != "q_lane"), got
            written = part_rates.parts_line(open(p(f"{name}_out")).read().split("\n"), D)[1]
            assert written[scale_part] == expect and sum(written) == expect, written
    print("part_rates polar: octaves known from their ratio, the edges, the clamps, a part with no fall at 0")
    print("part_rates polar: equal polarization is the fixed point; a part's doubled travel stands two octaves above the floor")


if __name__ == "__main__":
    main()
