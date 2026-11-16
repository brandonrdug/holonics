#!/usr/bin/env -S python3 -I
"""Controls for tools/tension_ruler.py (gate 1): the locator recovers a planted product on a held half (a ruler's null is held to a
planted law, CLAUDE.md, Method), a table's rows name their places, and a value digit's kind is read from its record."""
import os
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tension_ruler as t


def planted():
    rng = np.random.default_rng(1)
    n, d = 8000, 12
    r = rng.standard_normal((n, d))
    rb = np.hstack([r, np.ones((n, 1))])
    a0 = rng.standard_normal(d + 1) + 1j * rng.standard_normal(d + 1)
    b0 = rng.standard_normal(d + 1) + 1j * rng.standard_normal(d + 1)
    p = (rb @ a0) * (rb @ b0)
    lam = np.stack([p.real, p.imag], axis=1) @ rng.standard_normal((2, 6)) + 0.1 * rng.standard_normal((n, 6))
    fit = np.arange(n) < n // 2
    a, b = t.locate(r[fit], lam[fit], 1, sweeps=12)
    share = t.removed(t.products_of(r, a, b), lam, fit, ~fit)
    assert share > 0.98, f"a planted product located at {share:.3f} of its covector on the held half"
    # A covector the chart does not hold: nothing is located on the held half.
    noise = rng.standard_normal((n, 6))
    a, b = t.locate(r[fit], noise[fit], 2, sweeps=6)
    share = t.removed(t.products_of(r, a, b), noise, fit, ~fit)
    assert share < 0.02, f"products located on noise remove {share:.3f} on the held half"


def kinds():
    # 195 + 27 = 222: the units place is carried out of, the tens place carried into, the hundreds held by one operand and carried into.
    label = "tension:met:+:195:27:222"
    assert t.part_of(t.place_kind(label, 2)) == "units"
    assert t.part_of(t.place_kind(label, 1)) == "both-carry"
    assert t.part_of(t.place_kind(label, 0)) == "one-carry"
    assert t.place_kind(label, 1)[4:7] == (9, 2, 2)
    # 5 + 7 = 12: the value's first digit is the carry out.
    assert t.part_of(t.place_kind("tension:met:+:5:7:12", 0)) == "top"
    # 40 - 215 = -175: the larger operand's digits lead, and the sign is no digit.
    label = "tension:met:-:40:215:-175"
    assert t.part_of(t.place_kind(label, 3)) == "units"
    assert t.place_kind(label, 3)[4:7] == (5, 0, 5)
    # 215 - 40: the tens borrow, so the hundreds column, which one operand holds, is carried into.
    assert t.part_of(t.place_kind(label, 1)) == "one-carry"
    assert t.site_role(label, 0) == ("a", 1, 4) and t.site_role(label, 5) == ("b", 2, 2) and t.site_role(label, 14) == ("v", 0, 5)
    assert t.site_role(label, 11) == (None, -1, -1)


def table():
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, "t.tsv")
        t.table(out, "control", 20, 5, 2)
        rows = [line.rstrip("\n").split("\t") for line in open(out)]
        assert len(rows) == 25
        for label, prompt, run, places in rows:
            _, kind, op, a, b, v = label.split(":")
            assert prompt == f"{a} {op} {b} = " and run == f"{v}\\n"
            assert int(v) == (int(a) + int(b) if op == "+" else int(a) - int(b))
            assert len(a) <= 6 and len(b) <= 6 if kind == "met" else (7 <= len(a) <= 9 and 7 <= len(b) <= 9)
            where = [int(x) for x in places.split(",")]
            assert 1 <= len(where) <= 2 and all(v[j].isdigit() for j in where)


if __name__ == "__main__":
    planted()
    kinds()
    table()
    print("tension-ruler controls: ok")
