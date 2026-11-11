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
"""
import io
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import part_rates  # noqa: E402

D = {"alphabet": 5, "width": 16, "heads": 4, "modes": 2, "still": 2, "contacts": 16, "ticks": 4, "frames": 4, "reach": 16, "lanes": 2, "carry": False}
OLD_F = 8
KEYS = ("alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes")


def write(path, theta, octaves, d=D, extra=None):
    words = ["hnn-field-v14"] + [str(d[k]) for k in KEYS] + ["0"]
    with open(path, "w") as f:
        f.write("hnn-field-learner-v3 12 0 0 -\n" + " ".join(words) + "\n" + " ".join(str(int(x)) for x in theta) + "\n")
        if extra is not None:
            f.write(extra + "\n")
        f.write("parts " + " ".join(str(k) for k in [OLD_F] + octaves) + "\n")


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
        assert text[-2] == "parts " + " ".join(str(k) for k in [OLD_F] + moved) and text[-1] == ""
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
    print("part_rates: 4 lines, the controls hold")


if __name__ == "__main__":
    main()
