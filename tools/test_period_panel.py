#!/usr/bin/env -S python3 -I
"""Controls of period_panel.py on writes planted here (no state's write is read).

  form      a made row's prompt ends on a separator and holds whole lines, its reference repeats the last shown line, and only
            a bare row's shown lines repeat;
  kept      a write that is the called stretch reads meter1 = meter2 = 1 and a bare row's copy = 1;
  drawn     a write that keeps the timing with other letters reads the meters at 1 and copy at chance;
  none      a write of letters alone reads meter1 = 0, and a write of separators alone reads 0;
  shifted   the period kept one place late reads meter1 under 0;
  carry     spaces at every called separator and no newline read meter1 = 1 and meter2 = 0: a period without its carry;
  short     a write shorter than one line calls no break, so its meter2 reads `-` and is left out of what is kept.
"""
import os
import random
import sys
import tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import period_panel as pp

passed = 0


def check(cond, what):
    global passed
    if not cond:
        sys.exit(f"FAILED {what}")
    passed += 1


ROWS = list(pp.rows(7))
check(len(ROWS) == len(pp.LENGTHS) * len(pp.LINES) * 2 * pp.ROWS, "one row a length, a line, a kind and a draw")
for label, prompt, reference in ROWS:
    _, l, w, kind, _ = label.split(".")
    length, per_line = int(l[1:]), int(w[1:])
    check(prompt[-1] == ("\n" if per_line else " "), f"{label}: the prompt ends on its separator")
    check(len(prompt) % ((length + 1) * max(per_line, 1)) == 0, f"{label}: the prompt holds whole lines")
    check(all((k + 1) % (length + 1) == 0 or ch.islower() for k, ch in enumerate(prompt + reference)), f"{label}: letters between")
    check(all(ch in pp.SEPARATORS for ch in (prompt + reference)[length::length + 1]), f"{label}: a separator every P1 places")
    period = (length + 1) * max(per_line, 1)
    check(reference == (prompt[-period:] * len(reference))[:len(reference)], f"{label}: the reference repeats the last shown line")
    check((prompt[-2 * period:-period] == prompt[-period:]) == (kind == "bare"), f"{label}: only a bare row's shown lines repeat")
    check(pp.unescape(pp.escape(prompt)) == prompt, f"{label}: the escape returns")


def table(write):
    """The cells' lines of a forms.written whose written column is `write(label, prompt, reference)`."""
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "forms.written")
        with open(path, "w", encoding="utf-8") as f:
            f.write("other.row\tp\tw\tr\n")
            for label, prompt, reference in ROWS:
                f.write(f"{label}\t{pp.escape(prompt)}\t{pp.escape(write(label, prompt, reference))}\t{pp.escape(reference)}\n")
        out = pp.lines(pp.read(path))
    cells = {}
    for line in out[:-1]:
        f = dict(x.split("=") for x in line.split()[1:])
        cells[(int(f["L"]), int(f["W"]), f["kind"])] = f
    return cells, out[-1]


rng = random.Random(3)
letters = lambda ref: "".join(ch if ch in pp.SEPARATORS else rng.choice("abcdefghijklmnopqrstuvwxyz") for ch in ref)

cells, kept = table(lambda label, prompt, reference: reference)
check(len(cells) == len(pp.LENGTHS) * len(pp.LINES) * 2, "a line a cell")
check(all(f["rows"] == str(pp.ROWS) for f in cells.values()), "every draw of a cell is read, and no other row")
check(all(f["meter1"] == "1.000" for f in cells.values()), "kept: meter1 is 1")
check(all(f["meter2"] in ("1.000", "-") for f in cells.values()), "kept: meter2 is 1 where a break is called")
check(all((f["meter2"] == "-") == (w == 0 or w * (l + 1) > len(next(r for lab, _, r in ROWS if lab.startswith(f"per.L{l}.W{w}."))))
          for (l, w, _), f in cells.items()), "meter2 is `-` only where no break is called")
check(all(f["copy"] == "1.000" for (_, _, kind), f in cells.items() if kind == "bare"), "kept: a bare row's letters are copied")
check(kept.split()[1] == "P1=" + ",".join(str(l + 1) for l in pp.LENGTHS), "kept: every P1 is named")
check("120" not in kept.split()[2].split("=")[1].split(","), "a P2 no write reaches is not named as kept")

cells, kept = table(lambda label, prompt, reference: letters(reference))
check(all(f["meter1"] == "1.000" for f in cells.values()), "drawn: the timing alone keeps meter1 at 1")
check(all(float(f["copy"]) < 0.2 for (_, _, kind), f in cells.items() if kind == "bare"), "drawn: other letters copy at chance")

cells, kept = table(lambda label, prompt, reference: "".join("e" for _ in reference))
check(all(f["meter1"] == "0.000" for f in cells.values()), "none: letters alone read 0")
check(kept.split()[1] == "P1=-" and kept.split()[2] == "P2=-", "none: nothing is kept")
cells, _ = table(lambda label, prompt, reference: " " * len(reference))
check(all(f["meter1"] == "0.000" for f in cells.values()), "none: separators alone read 0")

cells, _ = table(lambda label, prompt, reference: "e" + reference[:-1])
check(all(float(f["meter1"]) < 0 for f in cells.values()), "shifted: the period one place late reads under 0")

cells, kept = table(lambda label, prompt, reference: reference.replace("\n", " "))
check(all(f["meter1"] == "1.000" for f in cells.values()), "carry: spaces at every separator keep meter1")
check(all(f["meter2"] in ("0.000", "-") for f in cells.values()), "carry: no newline reads meter2 = 0")
check(kept.split()[2] == "P2=-", "carry: no period of periods is kept")

cells, _ = table(lambda label, prompt, reference: reference[:4])
check(all(f["meter2"] == "-" for f in cells.values()), "short: a write under one line calls no break")

print(f"period_panel controls: {passed} checks passed")
