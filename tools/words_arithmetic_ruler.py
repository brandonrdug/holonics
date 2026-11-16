#!/usr/bin/env -S python3 -I
"""A ruler: the arithmetic the store's word problems hold, as counts (the lead, November 16).

Usage: words_arithmetic_ruler.py STORE [OCTETS]

Reads `STORE/DOCS_words.bin` (the training documents of the words slice; never the held yardstick) and prints three counts over its
first OCTETS octets (all of it where none is given):

- `WORDS_LENGTHS`: the numerals (maximal runs of decimal digits) by their length, one to nine digits;
- `WORDS_OPERANDS`: the lines that hold an arithmetic expression after an `=`, by the count of operands the expression joins (the count
  of its binary operators and one), two to six;
- `WORDS_OPS`: those lines' binary operators by kind (`+`, `-`, `*`, and `/` with `//` counted as `/`).

Why: the arithmetic world's records were drawn with operand lengths uniform over one to six digits and their operations uniform over
`+`, `-` and `*`, while the word problems the arithmetic serves hold numerals of one or two digits at more than four in five. The counts
are the weights `tools/arithmetic_world.py` draws a redrawn slice with (`--lengths`, `--operands`, `--ops`), so the terrain's shape is
read from the store and no weight is set by hand. A ruler: it names numerals and operators by the layout of the documents' text, outside
the machine, and only its counts leave the private store.
"""
import collections
import re
import sys

NUMERAL = re.compile(rb"\d+")
# A line with an expression after its `=`: names, numerals, parentheses, spaces and binary operators.
LINE = re.compile(rb"^[A-Za-z_][A-Za-z_0-9]* = ([A-Za-z_0-9 ().+\-*/]+)$", re.M)
OPERATOR = re.compile(rb"(?<=[A-Za-z_0-9)]) ?(//|\*\*|[+\-*/]) ?(?=[A-Za-z_0-9(])")


def main():
    store = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    with open(f"{store}/DOCS_words.bin", "rb") as f:
        data = f.read() if limit is None else f.read(limit)
    lengths = collections.Counter(min(len(m), 9) for m in NUMERAL.findall(data))
    operands, ops = collections.Counter(), collections.Counter()
    for expr in LINE.findall(data):
        found = OPERATOR.findall(expr)
        if not found or b"**" in found:
            continue
        operands[min(len(found) + 1, 6)] += 1
        for op in found:
            ops["/" if op == b"//" else op.decode()] += 1
    print(f"WORDS_READ octets={len(data)} numerals={sum(lengths.values())} expression_lines={sum(operands.values())} operators={sum(ops.values())}")
    print("WORDS_LENGTHS " + " ".join(f"{k}:{lengths[k]}" for k in range(1, 10)))
    print("WORDS_OPERANDS " + " ".join(f"{k}:{operands[k]}" for k in range(2, 7)))
    print("WORDS_OPS " + " ".join(f"{k}:{ops[k]}" for k in "+-*/"))


if __name__ == "__main__":
    main()
