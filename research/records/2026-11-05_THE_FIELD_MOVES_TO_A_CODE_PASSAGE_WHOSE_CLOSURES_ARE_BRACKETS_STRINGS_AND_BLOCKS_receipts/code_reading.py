#!/usr/bin/env python3
"""The written code beside the held code (the code passage, November 5): from a write's SAMPLE.tsv and the held passage.

Usage: code_reading.py HELD.txt SAMPLE.tsv

Over the written answers: bytes written over held and their correlation; how many open a code fence and close it; how many
whose code (inside the fence where there is one) parses as Python (`ast.parse`, an exterior reading that nothing in the
machine reads); its lines, and the share of its identifiers that stand in its question or in its held answer. The held
answers read the same as the reference. Aggregates only; nothing here is a text.
"""
import ast
import re
import statistics
import sys
import warnings

warnings.filterwarnings("ignore")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def records(path):
    data = open(path, "rb").read()
    out = []
    for r in data.split(b"\x1e"):
        if b"\x1f" in r:
            q, a = r.split(b"\x1f", 1)
            out.append((q.decode("utf-8", "replace"), a.decode("utf-8", "replace")))
    return out


def code_of(a):
    m = re.search(r"```(?:python)?\n(.*?)(?:```|$)", a, re.S)
    return m.group(1) if m else a


def parses(code):
    try:
        ast.parse(code)
        return True
    except Exception:
        return False


def read(pairs):
    fenced = sum("```" in a for _, a, _ in pairs)
    closed = sum(a.count("```") >= 2 for _, a, _ in pairs)
    ok = sum(parses(code_of(a)) for _, a, _ in pairs)
    lines = statistics.mean(code_of(a).count("\n") + 1 for _, a, _ in pairs)
    inq = inh = total = 0
    for q, a, h in pairs:
        qi, hi = set(IDENT.findall(q)), set(IDENT.findall(h))
        for w in IDENT.findall(code_of(a)):
            total += 1
            inq += w in qi
            inh += w in hi
    return f"{len(pairs)} answers: a fence opened {fenced}, closed {closed}; parses as Python {ok}; code lines mean {lines:.1f}; identifiers {total}, in the question {inq / max(total, 1):.2f}, in the held answer {inh / max(total, 1):.2f}"


def main():
    held = records(sys.argv[1])
    written = []
    for line in open(sys.argv[2], "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if k.isdigit():
            w = text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace").decode("utf-8", "replace")
            written.append((int(k), w))
    w_pairs = [(held[k][0], w, held[k][1]) for k, w in written]
    h_pairs = [(held[k][0], held[k][1], held[k][1]) for k, _ in written]
    wb = [len(w.encode()) for _, w in written]
    hb = [len(held[k][1].encode()) for k, _ in written]
    corr = statistics.correlation(wb, hb) if len(wb) > 2 else float("nan")
    print(f"bytes written/held {sum(wb) / sum(hb):.3f}, correlation {corr:+.3f}, {sum(w > h for w, h in zip(wb, hb))} longer, {sum(w < h for w, h in zip(wb, hb))} shorter")
    print("written:", read(w_pairs))
    print("held:   ", read(h_pairs))


if __name__ == "__main__":
    main()
