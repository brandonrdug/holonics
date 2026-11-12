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

The triads (theory, November 12; the triad record §4), on drawn states of declarations with two triads, without and with carry circles:
  layout     the head hnn-field-v14f (C written even at 0, then J); the charts, their biases and the return after every other family, every
             old offset unchanged; one part over the three, written after the first lane's letter rows; a v14f head with no triads refused;
  lines      a line of the written count reads back by its order, and a line without the triad's octave reads it at 0;
  update     a steady travel planted in the triad's entries moves its octave one faster and prints it beside the others;
  blocks     under the block law the triad's blocks are one unit at one rate: a travel twice the field's in all three families raises
             every triad entry two octaves, and no leg is printed alone.
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


def head_words(d):
    """The field's head line for d: hnn-field-v14, hnn-field-v14e with carry circles, hnn-field-v14f with triads (C written even at 0, then J)."""
    c, j = d.get("carry", 0), d.get("triads", 0)
    kind = "hnn-field-v14f" if j else "hnn-field-v14e" if c else "hnn-field-v14"
    return [kind] + [str(d[k]) for k in KEYS] + ["0"] + ([str(c)] if c or j else []) + ([str(j)] if j else [])


def write(path, theta, octaves, d=D, extra=None):
    words = head_words(d)
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
        run("open", p("c0"), str(OLD_F), ",".join(str(k) for k in [0] * len(part_rates.written(dc))), p("c1"))
        line = [l for l in open(p("c1")).read().split("\n") if l.startswith("parts ")][0]
        assert len(line.split(" ")) == 2 + len(part_rates.written(dc)) == 2 + 22, line
        held = part_rates.parts_line(open(p("c0")).read().split("\n"), dc)
        assert held[1][part_rates.PLAIN_PARTS:] == [0] * (part_rates.PARTS - part_rates.PLAIN_PARTS), "a sixteen-part line reads the circles' and the letter rows' parts at octave 0"
        got_c = run("update", p("c0"), p("c0"), p("c0"), p("c2"))
        assert set(got_c) == set(part_rates.PART_NAMES[q] for q in part_rates.written(dc)) and "triad" not in got_c, "a state with carry circles prints its twenty-two"
        assert len([l for l in open(p("c2")).read().split("\n") if l.startswith("parts ")][0].split(" ")) == 2 + len(part_rates.written(dc))
        with open(p("k"), "w") as f:
            f.write(open(p("s0")).read().replace("hnn-field-v14 ", "hnn-field-v14k ", 1).replace(" 0\n", " 0 1\n", 1))
        try:
            part_rates.load(p("k"))
        except AssertionError:
            pass
        else:
            raise AssertionError("the retired carry's head is not refused")
        # The leak's linear chart (hnn-field-v14t, retired November 12) is refused by the field; its states stay receipts this ruler reads, the
        # layout the same as the log chart's (hnn-field-v14e).
        with open(p("t"), "w") as f:
            f.write(open(p("c0")).read().replace("hnn-field-v14e ", "hnn-field-v14t ", 1))
        assert open(p("t")).read() != open(p("c0")).read()
        assert part_rates.load(p("t"))[1] == part_rates.load(p("c0"))[1], "a linear chart's receipt reads with the log chart's layout"
        print("part_rates carry: the circles' four parts, twenty-two written, sixteen read at octave 0, the retired head refused, the linear chart's receipts read")

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
        assert part_rates.expand(D, [0] * 16)[19:22] == [0, 0, 0] and part_rates.expand(dc, [0] * 19)[19:22] == [0, 0, 0]
        got_f = run("update", p("f0"), p("f0"), p("f0"), p("f1"))
        assert set(got_f) == set(part_rates.PART_NAMES[p] for p in part_rates.written(D)), "a field without circles prints its nineteen"
        print("part_rates first: the letter rows' three parts, nineteen written without circles, older lines read at octave 0")
        polar_controls(p)
        blocks_controls(p)
        triad_controls(p)
    print("part_rates: 17 lines, the controls hold")


def learner_text(path, theta, second, octaves, d=D, rate=12, own=None):
    """A learner's text with its moments' lines (first moments zero), for the law's controls; own, each entry's rate, a trailing rates line."""
    words = head_words(d)
    line = [octaves[p] for p in part_rates.written(d)]
    with open(path, "w") as f:
        f.write(f"hnn-field-learner-v3 {rate} 0 0 -\n" + " ".join(words) + "\n" + " ".join(str(int(x)) for x in theta) + "\n"
                + " ".join("0" for _ in theta) + "\n" + " ".join(str(int(x)) for x in second) + "\n" + "parts " + " ".join(str(k) for k in [OLD_F] + line) + "\n"
                + ("" if own is None else "rates " + " ".join(str(r) for r in own) + "\n"))


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



def fields_of(text, head):
    """The key=value words of the printed lines that begin with head, a dict a line."""
    return [{k: v for k, v in (w.split("=", 1) for w in l.split(" ")[1:] if "=" in w)} for l in text.split("\n") if l.startswith(head + " ")]


def blocks_controls(p):
    """[theory, November 12 00:20] The block law: every block a part of its own at its own rate, decided in rationals."""
    from fractions import Fraction as Fr
    import state_travel
    # The decision alone: signed octaves, a block with no fall one under its coolest, the bounds of an entry's rate, no floor.
    oc = part_rates.block_octave
    assert (oc(Fr(4), Fr(1), [0], 12), oc(Fr(1, 4), Fr(1), [0], 12), oc(Fr(1, 2), Fr(1), [3], 12)) == (2, -2, -1)
    assert oc(Fr(2**20), Fr(1), [0], 12) == 11 and oc(Fr(1, 2**300), Fr(1), [0], 12) == 12 - part_rates.WIDEST_RATE
    assert oc(Fr(-1), Fr(1), [-2, 0], 12) == -3 and oc(Fr(0), Fr(1), [3], 12) == 2
    assert oc(None, Fr(1), [0], 12) is None and oc(Fr(1), None, [0], 12) is None and oc(Fr(1), Fr(0), [0], 12) is None
    print("part_rates blocks: signed octaves from the ratio, no fall one under the coolest, an entry's rate from one bit to the carrier")

    fam, total = state_travel.layout(D)
    grain = [0] * total
    for _, at, shape, g in fam:
        n = 1
        for x in shape:
            n *= x
        for i in range(at, at + n):
            grain[i] = g
    at_of = {name: at for name, at, _, _ in fam}
    idx = {}
    for block, lane, contacts, _, family, mask in state_travel.scale_blocks(D, OLD_F):
        idx[(block, lane, contacts)] = [at_of[family] + j for j, m in enumerate(mask.ravel()) if m]
    q2, v2, pr2, temper = idx[("q", 2, "all")], idx[("v", 2, "all")], idx[("probe", 2, "all")], idx[("temper", 0, "all")]
    r1, r2 = idx[("read_rows", 1, "all")], idx[("read_rows", 2, "all")]
    zero = [0] * part_rates.PARTS

    def means(name, k=None, back=None, second=None, octaves=zero, own=None):
        """Four means: every entry travels k units on the first and the third travel (2 where k does not name it) and none between,
        back its third travel's sign; own[j] the rates line of mean j (None: none)."""
        k, back = k or {}, back or {}
        paths = []
        for j in range(4):
            theta = []
            for i in range(total):
                unit, ki = 1 << (grain[i] - 16), k.get(i, 2)
                theta.append(unit * (0 if j == 0 else ki if j < 3 else ki + back.get(i, 1) * ki))
            path = p(f"{name}_m{j}")
            learner_text(path, theta, second or [1 << 20] * total, octaves, own=None if own is None else own[j])
            paths.append(path)
        return paths

    def blocks(paths, state, out):
        text = io.StringIO()
        with redirect_stdout(text):
            part_rates.blocks(paths, state, out)
        got = {(f["block"], f["lane"], f["contacts"]): f for f in fields_of(text.getvalue(), "FIELD_BLOCK_RATE")}
        lines = open(out).read().split("\n")
        return got, fields_of(text.getvalue(), "FIELD_BLOCK_FLOOR")[0], lines, [int(x) for x in lines[-2].split(" ")[1:]]

    # Equal polarization everywhere is the floor itself: every block holds at the base word.
    paths = means("blk_flat")
    got, floor, lines, rates = blocks(paths, paths[3], p("blk_flat_out"))
    assert len(got) == len(idx) and all(f["octave"] == "0" and f["move"] == "hold" and f["window"] == "one" for f in got.values()), got
    assert floor["blocks"] == str(len(idx)) and rates == [12] * total
    assert lines[-2].startswith("rates ") and lines[-3] == open(paths[3]).read().split("\n")[-2] and lines[-1] == ""
    assert lines[:-2] == open(paths[3]).read().split("\n")[:-1], "every line of the state as it stands, the rates line after the parts line"
    print("part_rates blocks: equal polarization is the floor; the state is written whole with its rates line after its parts line")

    # A block that travels twice as far stands two octaves above the floor, half as far two under, one whose third travel goes back one
    # under, and one without heat (no second moment) holds.
    second = [0 if i in temper else 1 << 20 for i in range(total)]
    k = {**{i: 4 for i in q2}, **{i: 1 for i in v2}}
    paths = means("blk_moved", k=k, back={i: -1 for i in pr2}, second=second)
    got, floor, _, rates = blocks(paths, paths[3], p("blk_moved_out"))
    want = {("q", "2", "all"): ("2", "raise"), ("v", "2", "all"): ("-2", "cool"), ("probe", "2", "all"): ("-1", "cool"), ("temper", "0", "all"): ("0", "hold")}
    for key, f in got.items():
        assert (f["octave"], f["move"]) == want.get(key, ("0", "hold")), (key, f)
    assert got[("temper", "0", "all")]["heat"] == "0" and got[("temper", "0", "all")]["pi"] == "-"
    assert all(rates[i] == 10 for i in q2) and all(rates[i] == 14 for i in v2) and all(rates[i] == 13 for i in pr2)
    assert sum(1 for r in rates if r == 12) == total - len(q2) - len(v2) - len(pr2)
    print("part_rates blocks: twice the travel two octaves above, half two under, a travel that goes back one under, no heat holds")

    # The window: a block whose rate changed inside the four means holds and leaves the floor; a block four laps at one octave under the
    # base word whose polarization at that rate is the floor's comes back to it.
    own_a = [11 if i in q2 else 13 if i in v2 else 12 for i in range(total)]
    own_b = [13 if i in v2 else 12 for i in range(total)]
    paths = means("blk_window", k={i: 1 for i in v2}, own=[own_a, own_b, own_b, own_b])
    got, floor, _, rates = blocks(paths, paths[3], p("blk_window_out"))
    assert got[("q", "2", "all")]["window"] == "two" and got[("q", "2", "all")]["move"] == "window" and all(rates[i] == 12 for i in q2)
    assert got[("v", "2", "all")]["octave_was"] == "-1" and (got[("v", "2", "all")]["octave"], got[("v", "2", "all")]["move"]) == ("0", "raise")
    assert all(rates[i] == 12 for i in v2) and floor["blocks"] == str(len(idx) - 2)
    print("part_rates blocks: a window across a change of rate holds; a block at its own rate a window long is read at it")

    # A block that mixed parts under a parts line (the first lane's read rows: their columns past the lane are read_lane's) becomes one.
    raised = list(zero)
    raised[part_rates.PART_NAMES.index("read_lane")] = 1
    paths = means("blk_mixed", octaves=raised)
    got, floor, _, rates = blocks(paths, paths[3], p("blk_mixed_out"))
    assert got[("read_rows", "1", "all")]["octave_was"] == "0..1" and got[("read_rows", "1", "all")]["octave"] == "-1", got[("read_rows", "1", "all")]
    assert got[("read_rows", "2", "all")]["octave_was"] == "1" and got[("read_rows", "2", "all")]["octave"] == "-2"
    assert all(rates[i] == 13 for i in r1) and all(rates[i] == 14 for i in r2) and floor["blocks"] == str(len(idx) - 2)
    # The same rates carried as each entry's own (`own`) read the same.
    for j, path in enumerate(paths):
        run("own", path, p(f"blk_own{j}"))
    assert part_rates.own_line(open(p("blk_own3")).read().split("\n"), total) == part_rates.learner_rates(D, 12, (OLD_F, raised), None, total)
    again = blocks([p(f"blk_own{j}") for j in range(4)], p("blk_own3"), p("blk_own_out"))
    assert again[0] == got and again[3] == rates
    print("part_rates blocks: a block of two parts' rates is read at both and set at one; the parts' rates carried as each entry's own read the same")

    # Refusals: the octave verbs and the base word on a state with its own rates, four means at another base word, a standing file.
    state = p("blk_own3")
    for args in (("update", state, state, state, p("blk_x1")), ("means", state, state, state, state, p("blk_x2")),
                 ("open", state, str(OLD_F), ",".join("0" for _ in range(19)), p("blk_x3")), ("base", state, "11", p("blk_x4")),
                 ("own", state, p("blk_x5")), ("polar", state, state, state, state, state, p("blk_x6"))):
        try:
            run(*args)
        except AssertionError:
            pass
        else:
            raise AssertionError(f"not refused: {args[0]} on a state with its own rates")
    hot = p("blk_hot_m0")
    with open(hot, "w") as f:
        f.write(open(paths[0]).read().replace("hnn-field-learner-v3 12 ", "hnn-field-learner-v3 11 ", 1))
    for args in (([hot] + paths[1:], paths[3], p("blk_x7")), (paths, paths[3], p("blk_mixed_out"))):
        try:
            with redirect_stdout(io.StringIO()):
                part_rates.blocks(*args)
        except (AssertionError, FileExistsError):
            pass
        else:
            raise AssertionError(f"not refused: blocks writing {os.path.basename(args[2])}")
    assert not any(os.path.exists(p(f"blk_x{j}")) for j in range(1, 8))
    print("part_rates blocks: the octave verbs and the base word refuse a state with its own rates; another base word and a standing file are refused")


def triad_controls(p):
    """[theory, November 12; the triad record §4] The triads: the head, the layout, the one part, the lines and the block law's one unit."""
    import state_travel
    J, dw, T = 2, D["width"], part_rates.TRIAD_PART
    assert part_rates.PART_NAMES[T] == "triad" and part_rates.PARTS == 23
    for c in (0, 2):
        dp, dt = dict(D, carry=c), dict(D, carry=c, triads=J)
        fam0, total0 = part_rates.layout(dp)
        fam, total = part_rates.layout(dt)
        assert all(fam[k] == v for k, v in fam0.items()), "every old offset is unchanged"
        assert (fam["triad"], fam["triad_bias"], fam["w_triad"], total) == (total0, total0 + 6 * J * dw, total0 + 6 * J * dw + 6 * J, total0 + 6 * J * dw + 6 * J + dw * 2 * J)
        parts = part_rates.founded_parts(dt, OLD_F)
        assert parts[:total0] == part_rates.founded_parts(dp, OLD_F) and parts[total0:] == [T] * (total - total0), "the triad's three families are its one part"
        assert part_rates.written(dt) == part_rates.written(dp) + [T]
        # The head: C written even at 0, then J; the ruler reads it back, and the state_travel ruler reads the same declaration and layout.
        octaves = [0] * part_rates.PARTS
        octaves[T], octaves[part_rates.PART_NAMES.index("q_lane")] = 3, 1
        write(p(f"t{c}"), draws(total, 31), octaves, d=dt)
        text = open(p(f"t{c}")).read().split("\n")
        assert text[1].split(" ")[0] == "hnn-field-v14f" and text[1].split(" ")[-2:] == [str(c), str(J)], text[1]
        lines, d_read, _, theta = part_rates.load(p(f"t{c}"))
        assert d_read == dt and len(theta) == total
        assert state_travel.state(p(f"t{c}"))[0] == dt and state_travel.layout(dt)[1] == total
        # A line of the written count reads back by its order; one without the triad's octave reads it at 0.
        assert len(text[-2].split(" ")) == 2 + len(part_rates.written(dt)) and part_rates.parts_line(lines, dt)[1] == octaves
        short = [octaves[q] for q in part_rates.written(dp)]
        assert part_rates.expand(dt, short) == [0 if q == T else octaves[q] for q in range(part_rates.PARTS)], "a line without the triad's octave reads it at 0"
        assert part_rates.expand(dt, [0] * 16) == [0] * part_rates.PARTS
        # update: a steady travel in the triad's entries alone.
        base, step = draws(total, 41), draws(total, 43)
        states = [list(base), list(base), list(base)]
        for i in range(total0, total):
            states[1][i] += step[i]
            states[2][i] += 2 * step[i]
        for k, th in enumerate(states):
            write(p(f"t{c}_{k}"), th, octaves, d=dt)
        got = run("update", p(f"t{c}_0"), p(f"t{c}_1"), p(f"t{c}_2"), p(f"t{c}_u"))
        assert set(got) == set(part_rates.PART_NAMES[q] for q in part_rates.written(dt)), "a field with triads prints the triad beside the others"
        assert got["triad"]["c"] == "1.000000" and got["triad"]["move"] == "faster" and got["triad"]["rate_octaves"] == "4" and got["triad"]["entries"] == str(total - total0), got["triad"]
        moved = part_rates.parts_line(open(p(f"t{c}_u")).read().split("\n"), dt)[1]
        assert moved[T] == 4 and moved[part_rates.PART_NAMES.index("q_lane")] == 0
    # A v14f head with no triads is refused, by both rulers.
    with open(p("t_zero"), "w") as f:
        f.write(open(p("t0")).read().replace(f" 0 0 {J}\n", " 0 0 0\n", 1))
    for reader in (part_rates.load, state_travel.state):
        try:
            reader(p("t_zero"))
        except AssertionError:
            pass
        else:
            raise AssertionError("an hnn-field-v14f head with no triads is not refused")
    print("part_rates triad: the v14f head, the layout after every family, one part written last, lines without its octave read at 0, a head of no triads refused")

    # The block law: the triad's blocks are one unit at one rate.
    dt = dict(D, triads=J)
    fam, total = state_travel.layout(dt)
    grain, at_of = [0] * total, {name: at for name, at, _, _ in fam}
    for _, at, shape, g in fam:
        n = 1
        for x in shape:
            n *= x
        for i in range(at, at + n):
            grain[i] = g
    legs, units = set(), set()
    for block, lane, contacts, _, family, mask in state_travel.scale_blocks(dt, OLD_F):
        if state_travel.rate_unit(block, lane, contacts) == ("triad", 0, "all"):
            legs.add((block, lane))
            units.update(at_of[family] + j for j, m in enumerate(mask.ravel()) if m)
    assert units == set(range(at_of["triad"], total)), "the triad's unit is its three families whole"
    assert {b for b, _ in legs} == set(state_travel.TRIAD_BLOCKS)
    paths = []
    for j in range(4):
        theta = []
        for i in range(total):
            unit, k = 1 << (grain[i] - 16), (4 if i in units else 2)
            theta.append(unit * (0 if j == 0 else k if j < 3 else 2 * k))
        paths.append(p(f"tb_m{j}"))
        learner_text(paths[-1], theta, [1 << 20] * total, [0] * part_rates.PARTS, d=dt)
    out = io.StringIO()
    with redirect_stdout(out):
        part_rates.blocks(paths, paths[3], p("tb_out"))
    got = {(f["block"], f["lane"], f["contacts"]): f for f in fields_of(out.getvalue(), "FIELD_BLOCK_RATE")}
    assert not any(b in state_travel.TRIAD_BLOCKS for b, _, _ in got), "no leg of the triad is moved alone"
    assert (got[("triad", "0", "all")]["octave"], got[("triad", "0", "all")]["move"], got[("triad", "0", "all")]["entries"]) == ("2", "raise", str(len(units))), got[("triad", "0", "all")]
    assert all(f["octave"] == "0" for key, f in got.items() if key[0] != "triad")
    rates = [int(x) for x in open(p("tb_out")).read().split("\n")[-2].split(" ")[1:]]
    assert all(rates[i] == 10 for i in units) and all(rates[i] == 12 for i in range(total) if i not in units)
    print("part_rates triad blocks: the triad's legs, biases and return are one unit of the block law, raised together at one rate")


if __name__ == "__main__":
    main()
