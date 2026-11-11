#!/usr/bin/env -S python3 -I
"""Controls of founding_strength.py on drawn receipts (host arithmetic on text written here; no committed receipt is read).

Two small receipts and a declaration are written under a temporary root:
  sources     each kind of key reads its figure: NAME= after an anchor, PREFIX.NAME (the first line from the anchor that holds both),
              tok:N, col:N of a Markdown row, and the N-th slash-separated part, with thousands commas dropped;
  strength    bought = control - arm, nats = bought x places, strength = nats / entries, with entries summed from signed terms;
  partition   a founding read by quarter prints its quarters' nats, their sum and the whole; one read whole only says so;
  ranks       only foundings read alike (same laps, read and region) are ranked, strongest first, and a lone founding is not;
  refusals    quarters whose places differ from the whole's, a count that is not whole, a founding that adds no entries, some
              quarters read without the rest, an anchor that matches no line, and a cell count other than eight.
"""
import io
import os
import sys
import tempfile
from contextlib import redirect_stdout
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import founding_strength as fs  # noqa: E402

RECEIPT = """# a drawn receipt
## arm_a
LINE lap=-1 own=9.000000 places=40
LINE lap=0 own=2.500000 places=40 parts=1.250000/1.750000/2.750000/4.250000 quarter_places=10/10/12/8
COUNT entries=1,000 grown=1,200
## control_a
LINE lap=0 own=2.600000 places=40 parts=1.300000/1.800000/2.900000/4.300000
## arm_b
LINE lap=0 own=2.580000 places=40
COUNT entries=300 grown=400
| 7 | 2.400000 | 2.700000 |
tokens a 2.550000 c
"""


def run(declaration, root):
    """The ruler's print on a declaration, or the message it exits with."""
    path = Path(root) / "declaration.tsv"
    path.write_text(declaration)
    out = io.StringIO()
    old_argv, old_root = sys.argv, fs.ROOT
    sys.argv, fs.ROOT = ["founding_strength.py", str(path)], Path(root)
    try:
        with redirect_stdout(out):
            fs.main()
    except SystemExit as stop:
        return None, str(stop.code)
    finally:
        sys.argv, fs.ROOT = old_argv, old_root
    return out.getvalue(), None


def fields(line):
    return dict(w.split("=", 1) for w in line.split(" ")[1:] if "=" in w)


def row(*cells):
    return "\t".join(cells)


def main():
    passed = 0
    with tempfile.TemporaryDirectory() as root:
        (Path(root) / "r.txt").write_text(RECEIPT)
        old = fs.ROOT
        fs.ROOT = Path(root)
        try:
            # sources: each kind of key
            assert fs.figure("r.txt::^## arm_a::own")[0] == Fraction(9)  # the first own= from the anchor on: lap=-1
            assert fs.figure("r.txt::^## arm_a::LINE lap=0.own")[0] == Fraction(5, 2)
            assert fs.figure("r.txt::^## arm_a::parts::3")[0] == Fraction(11, 4)
            assert fs.figure("r.txt::^## arm_a::COUNT.entries") == (Fraction(1000), "r.txt:5")
            assert fs.figure("r.txt::^\\| 7 \\|::col:3")[0] == Fraction(27, 10)
            assert fs.figure("r.txt::^tokens::tok:2")[0] == Fraction(51, 20)
            passed += 6
        finally:
            fs.ROOT = old

        whole = ("1", "mean", "all", "+r.txt::^## arm_a::COUNT.grown ; -r.txt::^## arm_a::COUNT.entries",
                 "r.txt::^## arm_a::LINE lap=0.own", "r.txt::^## control_a::LINE lap=0.own", "r.txt::^## arm_a::LINE lap=0.places")
        quarters = [("1", "mean", f"q{k}", whole[3], f"r.txt::^## arm_a::LINE lap=0.parts::{k}",
                     f"r.txt::^## control_a::LINE lap=0.parts::{k}", f"r.txt::^## arm_a::LINE lap=0.quarter_places::{k}") for k in (1, 2, 3, 4)]
        b = ("1", "mean", "all", "+r.txt::^## arm_b::COUNT.grown ; -r.txt::^## arm_b::COUNT.entries",
             "r.txt::^## arm_b::LINE lap=0.own", "r.txt::^## control_a::LINE lap=0.own", "r.txt::^## arm_a::LINE lap=0.places")
        lone = ("2", "end", "all", b[3], "r.txt::^\\| 7 \\|::col:2", "r.txt::^\\| 7 \\|::col:3", "r.txt::^## arm_a::LINE lap=0.places")
        good = "\n".join(["# a comment", row("a", *whole)] + [row("a", *q) for q in quarters] + [row("b", *b), row("b", *lone)]) + "\n"
        out, stop = run(good, root)
        assert stop is None, stop
        lines = out.split("\n")
        s = {(f["founding"], f["laps"], f["read"], f["region"]): f for f in (fields(l) for l in lines if l.startswith("FOUNDING_STRENGTH "))}
        # strength: a whole, bought 0.1 a place on 40 places = 4 nats over 200 entries
        a = s[("a", "1", "mean", "all")]
        assert (a["entries"], a["bought"], a["nats"], a["strength"]) == ("200", "0.100000", "4.00", "0.020000"), a
        # a quarter: bought 0.15 on 12 places = 1.8 nats, 0.009 an entry
        q3 = s[("a", "1", "mean", "q3")]
        assert (q3["places"], q3["bought"], q3["nats"], q3["strength"]) == ("12", "0.150000", "1.80", "0.009000"), q3
        # b: bought 0.02 on 40 places = 0.8 nats over 100 entries
        assert s[("b", "1", "mean", "all")]["strength"] == "0.008000"
        assert s[("b", "2", "end", "all")]["bought"] == "0.300000"
        passed += 4
        # partition: 0.5 + 0.5 + 1.8 + 0.4 = 3.2 nats on the quarters against the whole's 4.0
        part = [l for l in lines if l.startswith("FOUNDING_PARTITION founding=a ")]
        assert len(part) == 1 and "quarter_places=40" in part[0] and "quarter_nats=0.50/0.50/1.80/0.40" in part[0], part
        assert "sum=3.20" in part[0] and "whole=4.00" in part[0] and "whole_less_sum=0.80" in part[0], part
        assert any(l.startswith("FOUNDING_PARTITION founding=b laps=1 read=mean quarters=unread") for l in lines)
        passed += 3
        # ranks: a over b at lap 1's mean; the lone lap-2 end is not ranked
        ranks = [l for l in lines if l.startswith("FOUNDING_RANK ")]
        assert ranks == ["FOUNDING_RANK laps=1 read=mean region=all a 0.020000 > b 0.008000"], ranks
        passed += 1

        # refusals
        wrong_places = quarters[:3] + [quarters[3][:6] + ("r.txt::^## arm_a::LINE lap=0.quarter_places::1",)]
        refusals = {
            "the quarters hold": "\n".join([row("a", *whole)] + [row("a", *q) for q in wrong_places]),
            "a count that is not whole": row("a", "1", "mean", "all", "+r.txt::^## arm_a::LINE lap=0.own", *whole[4:]),
            "a founding adds entries": row("a", "1", "mean", "all", "-r.txt::^## arm_b::COUNT.entries", *whole[4:]),
            "some quarters read, not all four": "\n".join([row("a", *whole), row("a", *quarters[0])]),
            "no line matches": row("a", "1", "mean", "all", whole[3], "r.txt::^## nowhere::own", *whole[5:]),
            "eight tab-separated cells": "\t".join(["a", *whole[:6]]),
        }
        for want, declaration in refusals.items():
            out, stop = run(declaration + "\n", root)
            assert out is None and stop is not None and want in stop, (want, stop)
            passed += 1
    print(f"founding_strength controls: {passed} passed")


if __name__ == "__main__":
    main()
