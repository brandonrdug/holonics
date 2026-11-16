#!/usr/bin/env -S python3 -I
"""A ruler for the arithmetic world's held reads (the theory thread's anchor and answer reads of Build A, November 16).

  forms_table.py make STORE OUT     writes OUT, the table `read-forms` reads (`label<TAB>prompt<TAB>run`, a line feed written `\\n`):
                                    each held sum of two operands (`HELD_FORMS_arithmetic.tsv`) after its symbols (`a + b = `), its words
                                    (`a plus b equals `) and its foil (`a plux b eqvals `), and each held record (`HELD_arithmetic.*`) cut
                                    after its `= `; the run is the value and its line feed.
  forms_table.py sum OUT LOG        sums a `read-forms` log over the table: by form and the operands' lengths (met: one to six digits, as
                                    training; far: seven to nine), by the digit's place counted from the value's last, and for sums of two
                                    operands by whether a carry entered the digit's column. Codes in millionths of a bit a place.

A ruler on the host, outside the machine: it writes the held forms and adds up what the reading printed; it never enters a law. The world is
synthetic (tools/arithmetic_world.py), so its forms and values are printed freely."""
import os
import sys
from collections import defaultdict

WORDS = {"+": "plus", "-": "minus", "*": "times"}


def esc(t):
    return t.replace("\n", "\\n")


def make(store, out):
    rows = []
    with open(os.path.join(store, "HELD_FORMS_arithmetic.tsv")) as f:
        head = f.readline().rstrip("\n").split("\t")
        for line in f:
            r = dict(zip(head, line.rstrip("\n").split("\t")))
            for form in ("symbols", "words", "foil"):
                rows.append((f"anchor:{r['lengths']}:{r['op']}:{form}:{r['held']}", r[form] + " ", r["value"] + "\n"))
    data = open(os.path.join(store, "HELD_arithmetic.bin"), "rb").read().decode()
    with open(os.path.join(store, "HELD_IDS_arithmetic.txt")) as f:
        ids = [l.strip() for l in f]
    records = data.splitlines(keepends=True)
    assert len(records) == len(ids), "a held file whose records and identifiers differ in count"
    for ident, rec in zip(ids, records):
        expr, value = rec.split(" = ")
        rows.append((f"answer:{ident.split(':')[0].split('-')[1]}:{ident.split(':')[1]}", expr + " = ", value))
    with open(out, "x") as f:
        for label, prompt, run in rows:
            f.write(f"{label}\t{esc(prompt)}\t{esc(run)}\n")
    print(f"FORMS_TABLE rows={len(rows)}")


def carries(a, b, op, places):
    """For a + b (or a − b, as a borrow), whether column j (from the last digit) took a carry from column j − 1."""
    if op == "-" and a < b:
        a, b = b, a
    out = []
    for j in range(places):
        m = 10**j
        if op == "+":
            out.append(j > 0 and (a % m) + (b % m) >= m)
        elif op == "-":
            out.append(j > 0 and (a % m) < (b % m))
        else:
            out.append(None)
    return out


def total(xs):
    return sum(c for c, _ in xs), sum(n for _, n in xs)


def summ(table, log):
    rows = {}
    for line in open(table):
        label, prompt, run = line.rstrip("\n").split("\t")
        rows[label] = (prompt.replace("\\n", "\n"), run.replace("\\n", "\n"))
    sums = defaultdict(list)
    for line in open(log):
        if not line.startswith("FORMS_ROW "):
            continue
        f = dict(kv.split("=", 1) for kv in line.split()[1:])
        label = f["label"]
        prompt, run = rows[label]
        codes = [int(c) for c in f["by_place"].split(",")]
        value = run.rstrip("\n")
        digits = value.lstrip("-")
        kind = label.split(":")
        if kind[0] == "anchor":
            _, lengths, op, form, _ = kind
            key = (form, lengths)
            a, b = (int(x) for x in prompt.split()[::2][:2])
        else:
            _, lengths, _ = kind
            key = ("answer", lengths)
            op, a, b = None, None, None
            parts = prompt.split()
            if len(parts) == 4 and "(" not in prompt:
                a, op, b = int(parts[0]), parts[1], int(parts[2])
        sums[key + ("all",)].append((sum(codes), len(codes)))
        sums[key + ("feed",)].append((codes[-1], 1))
        nd = len(digits)
        cs = carries(a, b, op, nd) if op in ("+", "-") else [None] * nd
        for i, ch in enumerate(value):
            if ch == "-":
                sums[key + ("sign",)].append((codes[i], 1))
                continue
            j = len(value) - 1 - i
            sums[key + (f"digit{min(j, 6)}",)].append((codes[i], 1))
            if i == len(value) - nd:
                sums[key + ("lead",)].append((codes[i], 1))
            if op in ("+", "-") and j > 0:
                sums[key + (f"{op}carry" if cs[j] else f"{op}clear",)].append((codes[i], 1))
            if op in ("+", "-") and j == 0:
                sums[key + (f"{op}units",)].append((codes[i], 1))
    for key in sorted(sums):
        c, n = total(sums[key])
        print(f"FORMS_SUM form={key[0]} lengths={key[1]} part={key[2]} places={n} code={c // n if n else 0}")


if __name__ == "__main__":
    if sys.argv[1] == "make":
        make(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "sum":
        summ(sys.argv[2], sys.argv[3])
    else:
        sys.exit(__doc__)
