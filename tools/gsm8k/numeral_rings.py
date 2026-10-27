"""Whether a tower's carried modes hold a numeral's residues: an exterior exact probe on rings.

An exterior reading, never learner material, and no floats. Record:
research/records/2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md

    python3 -I tools/gsm8k/numeral_rings.py places KIND TEXT OUT [FIRST]
    python3 -I tools/gsm8k/numeral_rings.py probe KIND TRAIN TRAIN_CELLS HELD HELD_CELLS LEVELS MODES [FIRST] [modes=A:B]
    python3 -I tools/gsm8k/numeral_rings.py scale CELLS LEVELS MODES

`places` names places in every problem of TEXT (a run of problems separated by a blank line, a
question line then its answer lines), each a byte of the problem's framed text (a blank line, the
question, its line end, then the answer), the text `read-unit-tower-at` reads. OUT (create-new)
holds one place a line, the problem's index and the byte, tab-separated, in reading order; with
FIRST, of the first FIRST problems only (in `probe`, of TRAIN). KIND is
- `numerals`: the last digit of each whole numeral of three or more digits, labelled by its value
  (`numeral`). A numeral is a run of digits with no digit, `.` or `,` before it and no digit, nor
  `.` or `,` followed by a digit, after it;
- `equals`: the `=` of each calculation `<<a+b=` or `<<a-b=` of two whole numerals, labelled by
  `a`, by `b` and by the exact result (`result`): whether the state at the equals still holds the
  operand captured at the operator, the one read on past it, and their sum or difference.

`probe` reads the records `read-unit-tower-at` wrote for TRAIN's and HELD's places (LE u32 the
place's line, then LEVELS x MODES (re, im) LE i64 carried modes) and, for each level, each label
and each ring m in 9, 10, 11 (where ten turns, collapses and reflects) and 7, 13, 100 (where one
plane cannot hold the residue, and the last two digits), fits a nearest class mean on TRAIN's cells
labelled by the label modulo m and names HELD's cells (`argmin_c sum_k (n_c x_k - S_ck)^2 / n_c^2`,
compared exactly, ties to the smaller residue). Each line prints, out of the held-out cells, how
many it names right (`modes`), the same probe on each mode's energy `re^2 + im^2`, which is blind
to the phase (`energy`), the most frequent training residue named every time (`majority`), the
residue most frequent among training labels with the same last two digits (`suffix`, what those
digits alone name), and the modes probe read against the residue of the held-out cell half the list
away, so in another problem (`foil`; a result's numeral is written twice in a row).
With `modes=A:B` the probe reads only modes `A..B` of each level (the strands' written modes, record
research/records/2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md
§6), so what those modes hold is read apart from the modes beside them.

`scale` prints, for each level of the records in CELLS, every mode's largest and root-mean-square
modulus over the cells, `mode:max/rms`, in 256ths of amplitude one (the state's grain `2^(−24)`,
each modulus the integer square root of `re^2 + im^2`, the mean's root floored): how loud each
mode is where the probe reads it.
"""

import operator
from math import isqrt as math_isqrt
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "listener"))
import probe  # noqa: E402  the exact class-mean probe and its record reader

NUMERAL = re.compile(rb"(?<![\d.,])\d{3,}(?![\d]|[.,]\d)")
RINGS = (9, 10, 11, 7, 13, 100)


def problems_of(text):
    """The problems as `read-unit-tower-at` splits them: (question, answer) pairs."""
    out = []
    for p in text.split(b"\n\n"):
        if p.strip(b"\n"):
            q, _, a = p.partition(b"\n")
            out.append((q, a + b"\n" if not a.endswith(b"\n") else a))
    return out


EQUALS = re.compile(rb"<<(\d+)([+\-])(\d+)=")


def named(kind, text, first=None):
    """Every place: (problem, byte in the framed text, {label: value})."""
    found = []
    for i, (q, a) in enumerate(problems_of(text)[:first]):
        framed = b"\n\n" + q + b"\n" + a
        if kind == "numerals":
            found.extend((i, m.end() - 1, {"numeral": int(m.group())}) for m in NUMERAL.finditer(framed))
        elif kind == "equals":
            for m in EQUALS.finditer(framed):
                x, y = int(m.group(1)), int(m.group(3))
                found.append((i, m.end() - 1, {"a": x, "b": y, "result": x + y if m.group(2) == b"+" else x - y}))
        else:
            raise SystemExit(f"KIND is numerals or equals, not {kind}")
    return found


def cells(path, places, levels, modes, span=None):
    """Each level's modes and energies at every place, beside the place's labels; with `span`
    `(a, b)`, only modes `a..b` of each level."""
    _, state, _ = probe.faces(path, 0, levels, modes)
    if [c for c, _ in state] != list(range(len(places))):
        raise SystemExit(f"{path}: the records do not hold the places in order")
    a, b = span or (0, modes)
    out = []
    for level in range(levels):
        part = [(v, x[2 * modes * level + 2 * a: 2 * modes * level + 2 * b]) for (_, _, v), (_, x) in zip(places, state)]
        energy = [(v, [x[2 * k] ** 2 + x[2 * k + 1] ** 2 for k in range(b - a)]) for v, x in part]
        out.append((part, energy))
    return out


def scale(path, levels, modes):
    """Per level, each mode's largest and root-mean-square modulus over the cells, in 256ths of
    amplitude one on the state's grain `2^(-24)`."""
    _, state, _ = probe.faces(path, 0, levels, modes)
    if not state:
        raise SystemExit(f"{path}: no cells")
    lines = []
    for level in range(levels):
        loud = []
        for k in range(modes):
            at = 2 * modes * level + 2 * k
            e = [x[at] ** 2 + x[at + 1] ** 2 for _, x in state]
            loud.append(f"{k}:{math_isqrt(max(e)) >> 16}/{math_isqrt(sum(e) // len(e)) >> 16}")
        lines.append(f"NUMERAL_SCALE cells={path} level={level} n={len(state)} modes(mode:max/rms,1/256) {' '.join(loud)}")
    return lines


def named_right(train, held, m):
    """`probe.nearest_mean` with its square expanded: the cell's own `sum_k x_k^2` is common to every
    class, so a class scores `(sum_k S_ck^2 - 2 n_c x.S_c) / n_c^2`, compared exactly."""
    labels, n, sums = probe.fit([(v % m, x) for v, x in train], len(train[0][1]))
    square = {c: sum(s * s for s in sums[c]) for c in labels}

    def name(x):
        return min(labels, key=lambda c: (Fraction(square[c] - 2 * n[c] * sum(map(operator.mul, x, sums[c])), n[c] * n[c]), c))

    names = [name(x) for _, x in held]
    return names, sum(c == v % m for c, (v, _) in zip(names, held))


def suffix_right(train, held, m):
    by = {}
    for v, _ in train:
        by.setdefault(v % 100, {}).setdefault(v % m, 0)
        by[v % 100][v % m] += 1
    whole = {}
    for v, _ in train:
        whole[v % m] = whole.get(v % m, 0) + 1
    majority = min(whole, key=lambda r: (-whole[r], r))
    right = 0
    for v, _ in held:
        counts = by.get(v % 100, whole)
        right += min(counts, key=lambda r: (-counts[r], r)) == v % m
    return sum(v % m == majority for v, _ in held), right


def main(argv):
    if len(argv) in (5, 6) and argv[1] == "places":
        out = Path(argv[4])
        first = int(argv[5]) if len(argv) == 6 else None
        rows = "".join(f"{i}\t{b}\n" for i, b, _ in named(argv[2], Path(argv[3]).read_bytes(), first))
        with open(out, "x") as f:
            f.write(rows)
        print(f"PLACES kind={argv[2]} text={argv[3]} places={rows.count(chr(10))} out={out}")
    elif len(argv) in (9, 10, 11) and argv[1] == "probe":
        kind, levels, modes = argv[2], int(argv[7]), int(argv[8])
        rest = argv[9:]
        span = None
        if rest and rest[-1].startswith("modes="):
            a, _, b = rest.pop()[len("modes="):].partition(":")
            span = (int(a), int(b))
            if not 0 <= span[0] < span[1] <= modes:
                raise SystemExit(f"modes={a}:{b} is not a span of the {modes} modes")
        if len(rest) > 1:
            sys.exit(__doc__)
        first = int(rest[0]) if rest else None
        train = cells(argv[4], named(kind, Path(argv[3]).read_bytes(), first), levels, modes, span)
        held = cells(argv[6], named(kind, Path(argv[5]).read_bytes()), levels, modes, span)
        for level in range(levels):
            (tm, te), (hm, he) = train[level], held[level]
            for label in tm[0][0]:
                tml, tel = [(v[label], x) for v, x in tm], [(v[label], x) for v, x in te]
                hml, hel = [(v[label], x) for v, x in hm], [(v[label], x) for v, x in he]
                for m in RINGS:
                    names, right = named_right(tml, hml, m)
                    _, energy = named_right(tel, hel, m)
                    majority, suffix = suffix_right(tml, hml, m)
                    half = len(hml) // 2
                    foil = sum(n == hml[(i + half) % len(hml)][0] % m for i, n in enumerate(names))
                    only = f" modes={span[0]}:{span[1]}" if span else ""
                    print(
                        f"NUMERAL_RINGS cells={argv[6]}{only} kind={kind} label={label} level={level} mod={m} "
                        f"held={len(hml)} train={len(tml)} modes={right} energy={energy} "
                        f"majority={majority} suffix={suffix} foil={foil}"
                    )
    elif len(argv) == 5 and argv[1] == "scale":
        for line in scale(argv[2], int(argv[3]), int(argv[4])):
            print(line)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv)
