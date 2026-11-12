#!/usr/bin/env -S python3 -I
"""Controls of seen_passage.py on drawn passages (host arithmetic on text written here; no private passage is read).

  mix        the mixer is the splitmix64 step: from state 0 its first four outputs, and from 1234567 its first, are the reference
             generator's published values;
  records    the passage of field_train.rs's own records test reads as two problems with its blank lines kept, and a record without
             US or with an empty side is not a problem;
  split      as sections_of: the withheld are the problems of the smallest keys, the trained the rest, disjoint and whole, the same at
             every call;
  match      SEEN holds no withheld problem and none twice, each the nearest by answer bytes, then question bytes, then index;
             fewer trained problems than held ones are refused;
  files      the two passages are written under a new directory and read back to the chosen problems; a standing directory is
             refused.
"""
import contextlib
import io
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import seen_passage as sp  # noqa: E402

PASSED = []


def check(name, condition):
    if not condition:
        raise SystemExit(f"FAILED {name}")
    PASSED.append(name)


def main():
    reference = [0xE220A8397B1DCDAF, 0x6E789E6AA1B965F4, 0x06C45D188009454F, 0xF88BB8A8724C81EC]
    check("mix from state 0", [sp.mix(0, k) for k in range(1, 5)] == reference)
    check("mix from 1234567", sp.mix(1234567, 1) == 6457827717110365317)

    text = b"Add two numbers\nin Python\x1f```python\ndef add(a, b):\n\n    return a + b\n```\x1eSay hi\x1fprint('hi')\x1e"
    problems = sp.problems_of(text)
    check("records read", problems == [(b"Add two numbers\nin Python", b"```python\ndef add(a, b):\n\n    return a + b\n```"), (b"Say hi", b"print('hi')")])
    check("records skipped", sp.problems_of(b"no unit\x1e\x1fempty question\x1eempty answer\x1f\x1eq\x1fa\x1e") == [(b"q", b"a")])
    check("seed is the last word", sp.seed_of(b"\x00" * 5 + (258).to_bytes(8, "big")) == 258)

    held, trained = sp.withheld_of(40, 9, 11)
    keys = sorted(range(40), key=lambda i: (sp.mix(11, (1 << 61) | i), i))
    check("split sizes", len(held) == 9 and len(trained) == 31)
    check("split whole and disjoint", sorted(held + trained) == list(range(40)))
    check("split is the smallest keys", held == sorted(keys[:9]))
    check("split keyed, not drawn afresh", sp.withheld_of(40, 9, 11) == (held, trained))

    drawn = [(b"q" * (1 + i % 5), b"a" * (3 + (i * 7) % 11)) for i in range(40)]
    dev = [(b"x" * 2, b"y" * 5), (b"x" * 4, b"y" * 5), (b"x", b"y" * 13), (b"x" * 3, b"y" * 4)]
    seen = sp.matched(dev, drawn, trained)
    check("match never withheld", not set(seen) & set(held))
    check("match never twice", len(set(seen)) == len(seen) == len(dev))
    unused = set(trained)
    for (q, a), s in zip(dev, seen):
        best = min(unused, key=lambda i: (abs(len(drawn[i][1]) - len(a)), abs(len(drawn[i][0]) - len(q)), i))
        check("match nearest", s == best)
        unused.remove(s)
    try:
        sp.matched(dev, drawn, trained[:3])
        check("match refuses too few", False)
    except SystemExit:
        check("match refuses too few", True)

    with tempfile.TemporaryDirectory() as root:
        paths = {name: os.path.join(root, name) for name in ("TRAIN", "DEV", "KEYS")}
        for name, data in (("TRAIN", sp.passage(drawn)), ("DEV", sp.passage(dev)), ("KEYS", b"\x00" * 24 + (11).to_bytes(8, "big"))):
            with open(paths[name], "wb") as f:
                f.write(data)
        out = os.path.join(root, "OUT")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            sp.main(["seen_passage.py", paths["TRAIN"], paths["DEV"], paths["KEYS"], out])
        held4, trained4 = sp.withheld_of(40, 4, 11)
        withheld_read = sp.problems_of(open(os.path.join(out, "WITHHELD.txt"), "rb").read())
        seen_read = sp.problems_of(open(os.path.join(out, "SEEN.txt"), "rb").read())
        check("files withheld", withheld_read == [drawn[i] for i in held4])
        check("files seen", seen_read == [drawn[i] for i in sp.matched(dev, drawn, trained4)])
        check("files counts printed", "SEEN_PASSAGE train_problems=40 trained=36 withheld=4 dev=4" in printed.getvalue())
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                sp.main(["seen_passage.py", paths["TRAIN"], paths["DEV"], paths["KEYS"], out])
            check("files refuse a standing directory", False)
        except FileExistsError:
            check("files refuse a standing directory", True)
    print(f"seen_passage controls: {len(PASSED)} passed")


if __name__ == "__main__":
    main()
