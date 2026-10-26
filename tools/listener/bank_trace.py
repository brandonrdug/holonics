#!/usr/bin/env python3
"""Where a bank's read at an answer's opening is addressed, read from `read-tower-bank-trace` output.

    python3 -I tools/listener/bank_trace.py requests HEARD TEXT OUT
    python3 -I tools/listener/bank_trace.py share HEARD TEXT TRACE

An exterior observer's reads; nothing here enters the machine. TEXT is GSM8K problems separated by a
blank line, each a question line and its answer. A problem is named when its question's first word
(a run of letters) is capitalised and HEARD holds that word capitalised more often than in lower
case: the heard text's own reading of a proper name, with no list of names.

- `requests`: for each named problem, one request `p f`: the read at the answer's first byte `p`,
  and a window from the problem's first byte `f`, so the trace's window holds every cell of the
  question.
- `share`: for each request read, the cell whose arrival holds the problem's first byte (the name's
  cell, the class holding byte `f`) beside where the read is addressed: the share of reads whose largest
  address `|a|²` falls on the name's cell, and whose largest share `|a|² ‖w‖²` does; where the
  largest address falls otherwise (the read's own cell, another cell of the question, an earlier
  problem); the name cell's rank among the window's addresses, and the chance a uniform rank would
  give, `1/n` over the window's `n` cells. Split by whether the answer opens with the name.
"""
import collections
import re
import sys

LETTERS = re.compile(rb"[A-Za-z]+")


def problems(text):
    for m in re.finditer(rb"(?s).+?(?:\n\n|\Z)", text):
        yield m.start(), m.group()


def named(heard, text):
    counts = collections.Counter(LETTERS.findall(heard))
    for start, p in problems(text):
        question, newline, answer = p.partition(b"\n")
        m = LETTERS.match(question)
        if not newline or not answer or not m:
            continue
        w = m.group()
        if w[:1].isupper() and counts[w] > counts[w.lower()]:
            yield start, start + len(question) + 1, w, answer.startswith(w)


def requests(heard, text, out):
    with open(out, "x") as f:
        n = 0
        for start, opening, _, _ in named(heard, text):
            f.write(f"{opening}\t{start}\n")
            n += 1
    print(f"REQUESTS named_problems={n} out={out}")


def trace_of(path):
    reads, rows = {}, collections.defaultdict(list)
    for line in open(path):
        k = line.rstrip("\n").split("\t")
        if k[0] == "R":
            reads[int(k[1])] = tuple(int(x) for x in k[2:])
        else:
            p, place, ar, ai, w2 = (int(x) for x in k[1:])
            rows[p].append((place, ar * ar + ai * ai, w2))
    return reads, rows


def share(heard, text, path):
    reads, rows = trace_of(path)
    tally = collections.defaultdict(collections.Counter)
    ranks = collections.defaultdict(list)
    for start, opening, word, opens in named(heard, text):
        if opening not in reads:
            continue
        read_place, name_place, nonzero, largest, largest_share = reads[opening]
        window = rows[opening]
        present = max((r[0] for r in window), default=None)
        for kind in ("all", "answer opens with the name" if opens else "answer opens otherwise"):
            t = tally[kind]
            t["reads"] += 1
            t["largest address on the name"] += largest == name_place
            t["largest share on the name"] += largest_share == name_place
            where = ("the name" if largest == name_place else "the read's own cell" if largest == present
                     else "another cell of the question" if largest >= name_place else "an earlier problem")
            t[f"largest address on {where}"] += 1
            # A cell with no row has a zero address: it ranks last.
            order = [r[0] for r in sorted(window, key=lambda r: (-r[1], -r[0]))]
            cells = len({r[0] for r in window} | {name_place})
            ranks[kind].append((1 + order.index(name_place) if name_place in order else cells, cells))
    for kind in ("all", "answer opens with the name", "answer opens otherwise"):
        t, r = tally[kind], ranks[kind]
        if not t["reads"]:
            continue
        n = t["reads"]
        print(f"{kind}: {n} reads")
        for key in sorted(k for k in t if k != "reads"):
            print(f"  {key:<45} {t[key]:6d}  {t[key] / n:.4f}")
        mean_rank = sum(a for a, _ in r) / len(r)
        chance = sum(1 / b for _, b in r) / len(r)
        cells = sum(b for _, b in r) / len(r)
        first = sum(a == 1 for a, _ in r) / len(r)
        print(f"  the name's rank among the window's addresses: mean {mean_rank:.2f} of {cells:.1f} cells; first {first:.4f}; a uniform rank would be first {chance:.4f}")


def main():
    read = lambda p: open(p, "rb").read()
    command, args = (sys.argv[1], sys.argv[2:]) if len(sys.argv) > 1 else ("", [])
    if command == "requests" and len(args) == 3:
        requests(read(args[0]), read(args[1]), args[2])
    elif command == "share" and len(args) == 3:
        share(read(args[0]), read(args[1]), args[2])
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
