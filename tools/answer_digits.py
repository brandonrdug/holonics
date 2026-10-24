"""Read a tower's free writing (the sample-tower command's output, raw or as its TOWER_SAMPLE_TEXT
line) for the equations it writes, and count by operation how each written result's digits stand
against the true result's: its length (whether the result expands past its operands, holds their
length or contracts below it, and whether the writing does the same), its leading digit, its units
digit and, for sums and differences, its tens digit, with the tens split by whether the operands'
units carry (or borrow) and whether the written tens takes that carry. A line counts only when it is
a whole equation, `a op b = c` and nothing else, with a true result that is not negative. The prompt's
open line is prefixed so the first written result is read with its operands. An exterior reading,
outside the machine.

usage: python3 -I answer_digits.py OPEN_LINE WRITE [WRITE ...]
(OPEN_LINE: the prompt's last line, which the writing continues, e.g. `74-72=`)
"""
import re
import sys
from collections import Counter, defaultdict

EQ = re.compile(r"^(\d+)([+\-*])(\d+)=(\d+)$")


def text_of(path):
    """The written bytes: a raw file as it is, a TOWER_SAMPLE file's quoted text unescaped."""
    s = open(path, encoding="utf-8", errors="replace").read()
    if not s.startswith("TOWER_SAMPLE"):
        return s
    for line in s.splitlines():
        if not line.startswith("TOWER_SAMPLE_TEXT "):
            continue
        q, out, i = line[len("TOWER_SAMPLE_TEXT "):], [], 1
        while i < len(q) and q[i] != '"':
            if q[i] != "\\":
                out.append(q[i])
                i += 1
                continue
            n = q[i + 1]
            if n == "u":
                j = q.index("}", i)
                out.append(chr(int(q[i + 3:j], 16)))
                i = j + 1
            else:
                out.append({"n": "\n", "t": "\t", "r": "\r", "0": "\0"}.get(n, n))
                i += 2
        return "".join(out)
    return ""


def shape(a, op, b, c):
    if op == "*":
        return "full" if len(c) == len(a) + len(b) else "short"
    m = max(len(a), len(b))
    return "expands" if len(c) > m else "contracts" if len(c) < m else "holds"


def main():
    opening, paths = sys.argv[1], sys.argv[2:]
    rows = []
    for path in paths:
        for line in (opening + text_of(path)).split("\n"):
            m = EQ.match(line)
            if not m:
                continue
            a, op, b, c = m.groups()
            t = int(a) + int(b) if op == "+" else int(a) - int(b) if op == "-" else int(a) * int(b)
            if t >= 0:
                rows.append((a, op, b, c, str(t)))
    print(f"equations {len(rows)} from {len(paths)} writes")
    by = defaultdict(Counter)
    for a, op, b, c, t in rows:
        z = by[(op, shape(a, op, b, t))]
        z["n"] += 1
        z["right"] += c == t
        z["length_right"] += len(c) == len(t)
        z["longer"] += len(c) > len(t)
        z["shorter"] += len(c) < len(t)
        z["leading_right"] += c[0] == t[0]
        z["units_right"] += c[-1] == t[-1]
    for key in sorted(by):
        print("LENGTH", "/".join(key), " ".join(f"{k}={v}" for k, v in by[key].items()))
    for op in "+-":
        units, tens = Counter(), Counter()
        for a, o, b, c, t in rows:
            if o != op or len(c) != len(t) or len(t) < 2:
                continue
            units[(int(c[-1]) - int(t[-1])) % 10] += 1
            tens[int(c[-2]) - int(t[-2])] += 1
        print("UNITS_OFF_MOD_10", op, " ".join(f"{k}:{units[k]}" for k in range(10)))
        print("TENS_OFF", op, " ".join(f"{k}:{v}" for k, v in sorted(tens.items())))
    for op in "+-":
        z = Counter()
        for a, o, b, c, t in rows:
            if o != op or len(a) != 2 or len(b) != 2 or len(c) != len(t) or len(t) < 2:
                continue
            a1, a0, b1, b0 = int(a[0]), int(a[1]), int(b[0]), int(b[1])
            sign = 1 if op == "+" else -1
            carried = a0 + b0 >= 10 if op == "+" else a0 < b0
            without, taken = (a1 + sign * b1) % 10, (a1 + sign * b1 + sign) % 10
            key = "carry" if carried else "none"
            z[(key, "n")] += 1
            z[(key, "tens_without_carry")] += int(c[-2]) == without
            z[(key, "tens_with_carry")] += int(c[-2]) == taken
        print("TENS_CARRY", op, " ".join(f"{k[0]}/{k[1]}={v}" for k, v in sorted(z.items())))


if __name__ == "__main__":
    main()
