#!/usr/bin/env -S python3 -I
"""A panel and its ruler on the host: does a write keep a period it was shown, and a period of periods?

Usage: python3 tools/period_panel.py make OUT.tsv [SEED]
       python3 tools/period_panel.py read FORMS_WRITTEN

`make` writes a forms table for `athena ... write-next` (`label<TAB>prompt<TAB>reference`, a newline written `\\n`). Each row shows
a stretch of drawn lowercase words, all of one length `L`, a space after each, so a separator stands every `P1 = L + 1` places;
with `W > 0` the separator after every `W`-th word is a newline, so a line break stands every `P2 = W (L + 1)` places: a period
and a period of that period, the second kept only by counting turns of the first. A `bare` row repeats one word (or one line),
so its letters carry the period too; a `drawn` row draws every word anew, so only the timing does. The prompt ends on a
separator, so the first written place opens a word, and the reference is the last shown line repeated: on a bare row the stretch
the period calls for, on a drawn row what a writer repeating its last line would give, where the text shown never repeated one.

`read` reads `write-next`'s `forms.written` (`label<TAB>prompt<TAB>written<TAB>reference`) and prints, a line a cell of rows
(L, W, kind): `meter1`, the share of called separator places that hold a separator less the share of the other places that hold
one (0 for a write with no timing, 1 for the period kept); `meter2`, the same for newlines at the called line breaks (`-` where
`W = 0`, and where the write is shorter than one line, so no break was called); and `copy`, the share of letter places that hold
the reference's letter (a drawn row's is the control: a line repeated that the text never repeated). Then every `P1` and every
`P2` whose meter stands at 0.5 or more over every cell that carries it.

Why (November 24, the record of that day on context as a calendar): a receiver reads no time, only counts of one cycle against
another, and a unit is kept as long as the store that counts it rings. The line's turned rings fade one e-fold a radian
whatever their period, her sharp contacts reach the near field and her far field stands at octaves, so past a few places a
displacement is read to its octave unless a carry circle counts it, and a line break after exactly `W` words asks for a count.
This panel reads that as the text she writes: timing apart from letters (the drawn rows), and a carry apart from a period
(`meter2` beside `meter1`). The lengths put `P1` on periods the line's two turned heads hold at its reach of 3,771 (3, 4, 9 and
16, of the dyadic tower's 2, 4, 16, 32, … and the triadic's 3, 9, 27, …) and off them (5, 7, 10, 15), so a ring's own period is
read beside its neighbours. It is a ruler on a terrain it draws itself; it reads no state and refuses
nothing. Its rows are drawn by `random.Random(SEED)` alone and hold no text of anyone's.
"""
import random
import sys

LENGTHS = (2, 3, 4, 6, 8, 9, 14, 15)
LINES = (0, 2, 4, 8)
ROWS = 4
SHOWN = 240
CALLED = 96
SEPARATORS = (" ", "\n")


def word(rng, n):
    return "".join(rng.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(n))


def stretch(rng, length, per_line, kind, words):
    """`words` words of `length` letters, a space after each and a newline after every `per_line`-th (none where it is 0)."""
    unit = max(per_line, 1)
    line = [word(rng, length) for _ in range(unit)]
    out = []
    for k in range(words):
        w = line[k % unit] if kind == "bare" else word(rng, length)
        out.append(w + ("\n" if per_line and (k + 1) % per_line == 0 else " "))
    return out


def rows(seed):
    rng = random.Random(seed)
    for length in LENGTHS:
        for per_line in LINES:
            for kind in ("bare", "drawn"):
                for r in range(ROWS):
                    unit = max(per_line, 1)
                    shown = max(2 * unit, -(-SHOWN // ((length + 1) * unit)) * unit)
                    called = -(-CALLED // (length + 1))
                    text = stretch(rng, length, per_line, kind, shown + called)
                    reference = "".join(text[shown - unit + k % unit] for k in range(called))
                    yield f"per.L{length}.W{per_line}.{kind}.r{r}", "".join(text[:shown]), reference


def escape(s):
    return s.replace("\n", "\\n")


def unescape(s):
    return s.replace("\\n", "\n").replace("\\t", "\t")


def score(label, written, reference):
    """One row's counts: called separators hit, called, other places holding one, other places; the same for newlines; letters."""
    _, l, w, kind, _ = label.split(".")
    length, per_line = int(l[1:]), int(w[1:])
    c = dict(hit1=0, call1=0, false1=0, rest1=0, hit2=0, call2=0, false2=0, rest2=0, same=0, letters=0)
    for k, ch in enumerate(written):
        sep = (k + 1) % (length + 1) == 0
        brk = sep and per_line > 0 and ((k + 1) // (length + 1)) % per_line == 0
        c["call1" if sep else "rest1"] += 1
        c["hit1" if sep else "false1"] += ch in SEPARATORS
        c["call2" if brk else "rest2"] += 1
        c["hit2" if brk else "false2"] += ch == "\n"
        if not sep:
            c["letters"] += 1
            c["same"] += k < len(reference) and ch == reference[k]
    return (length, per_line, kind), c


def share(a, b):
    return a / b if b else 0.0


def read(path):
    cells = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            w = line.rstrip("\n").split("\t")
            if len(w) != 4 or not w[0].startswith("per."):
                continue
            key, c = score(w[0], unescape(w[2]), unescape(w[3]))
            cell = cells.setdefault(key, dict(rows=0))
            cell["rows"] += 1
            for name, v in c.items():
                cell[name] = cell.get(name, 0) + v
    return cells


def lines(cells):
    out, best1, best2 = [], {}, {}
    for (length, per_line, kind), c in sorted(cells.items()):
        m1 = share(c["hit1"], c["call1"]) - share(c["false1"], c["rest1"])
        m2 = share(c["hit2"], c["call2"]) - share(c["false2"], c["rest2"]) if c["call2"] else None
        p1, p2 = length + 1, per_line * (length + 1)
        best1.setdefault(p1, []).append(m1)
        if m2 is not None:
            best2.setdefault(p2, []).append(m2)
        out.append(f"PERIOD_PANEL L={length} W={per_line} P1={p1} P2={p2 if per_line else '-'} kind={kind} rows={c['rows']} called1={c['call1']} "
                   f"called2={c['call2']} meter1={m1:.3f} meter2={'-' if m2 is None else f'{m2:.3f}'} copy={share(c['same'], c['letters']):.3f}")
    kept = lambda best: ",".join(str(p) for p, ms in sorted(best.items()) if min(ms) >= 0.5) or "-"
    out.append(f"PERIOD_PANEL_KEPT P1={kept(best1)} P2={kept(best2)} cells={len(cells)}")
    return out


if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "make":
        seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20261124
        with open(sys.argv[2], "x", encoding="utf-8") as f:
            for label, prompt, reference in rows(seed):
                f.write(f"{label}\t{escape(prompt)}\t{escape(reference)}\n")
    elif len(sys.argv) == 3 and sys.argv[1] == "read":
        print("\n".join(lines(read(sys.argv[2]))))
    else:
        sys.exit(__doc__)
