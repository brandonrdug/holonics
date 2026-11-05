#!/usr/bin/env python3
"""What the written answers carry (§16.47, Brandon's lens of November 5, 16:00): from a write's SAMPLE.tsv beside the
held problems.

Usage: carried.py HELD.txt SAMPLE.tsv

Over the written answers: the numbers written, the share that stand in the question, the share that stand in an earlier
line of the same answer (carried) and the share in neither; the calculator annotations `<<expr=value>>` whose expression
reads as arithmetic, and how many close (the expression's exact value is the stated value); the final line's number found
earlier in the answer. The same for the held answers as their reference. Aggregates only; nothing here is a text.
"""
import re
import sys
from fractions import Fraction

NUM = re.compile(r"\d+(?:\.\d+)?")


def problems_of(text):
    blocks, cur = [], []
    for line in text.split(b"\n"):
        if line == b"":
            blocks.append(cur); cur = []
        else:
            cur.append(line)
    blocks.append(cur)
    return [(b[0].decode("utf-8", "replace"), b"\n".join(b[1:]).decode("utf-8", "replace")) for b in blocks if len(b) >= 2]


def value(expr):
    if not re.fullmatch(r"[\d.+\-*/() ]+", expr) or not re.search(r"\d", expr):
        return None
    toks = re.findall(r"\d+(?:\.\d+)?|[+\-*/()]", expr)
    pos = 0
    def atom():
        nonlocal pos
        if pos < len(toks) and toks[pos] == "(":
            pos += 1; v = add()
            if pos >= len(toks) or toks[pos] != ")": raise ValueError
            pos += 1; return v
        if pos < len(toks) and NUM.fullmatch(toks[pos]):
            pos += 1; return Fraction(toks[pos - 1])
        raise ValueError
    def mul():
        nonlocal pos
        v = atom()
        while pos < len(toks) and toks[pos] in "*/":
            op = toks[pos]; pos += 1; r = atom()
            v = v * r if op == "*" else v / r
        return v
    def add():
        nonlocal pos
        v = mul()
        while pos < len(toks) and toks[pos] in "+-":
            op = toks[pos]; pos += 1; r = mul()
            v = v + r if op == "+" else v - r
        return v
    try:
        v = add()
        return v if pos == len(toks) else None
    except (ValueError, ZeroDivisionError):
        return None


def read(pairs):
    nums = inq = carried = neither = 0
    ann = arith = closed = 0
    finals = final_found = 0
    for q, a in pairs:
        qn = set(NUM.findall(q))
        seen = set()
        for line in a.split("\n"):
            for n in NUM.findall(line):
                nums += 1
                if n in qn: inq += 1
                elif n in seen: carried += 1
                else: neither += 1
            seen |= set(NUM.findall(line))
        for expr, val in re.findall(r"<<([^<>=]*)=([^<>]*)>>", a):
            ann += 1
            v = value(expr)
            if v is not None and NUM.fullmatch(val.strip()):
                arith += 1
                closed += v == Fraction(val.strip())
        last = a.split("\n")[-1]
        m = re.fullmatch(r"#### ?(\d+(?:\.\d+)?)", last.strip())
        if m:
            finals += 1
            final_found += m.group(1) in set(NUM.findall("\n".join(a.split("\n")[:-1])))
    return f"numbers {nums}: in the question {inq / nums:.2f}, carried from an earlier line {carried / nums:.2f}, in neither {neither / nums:.2f}; annotations {ann}, arithmetic {arith}, closed {closed}; final lines {finals}, their number written earlier {final_found}"


def main():
    held = problems_of(open(sys.argv[1], "rb").read())
    written = []
    for line in open(sys.argv[2], "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            w = text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace").decode("utf-8", "replace")
            written.append((held[int(k)][0], w, held[int(k)][1]))
    print("written:", read([(q, w) for q, w, _ in written]))
    print("held:   ", read([(q, h) for q, _, h in written]))


if __name__ == "__main__":
    main()
