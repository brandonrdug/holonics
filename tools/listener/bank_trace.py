#!/usr/bin/env python3
"""Where a bank's read at an answer's opening is addressed, read from `read-tower-bank-trace` output.

    python3 -I tools/listener/bank_trace.py requests HEARD TEXT OUT
    python3 -I tools/listener/bank_trace.py share HEARD TEXT TRACE
    python3 -I tools/listener/bank_trace.py role HEARD TEXT CELLS [CELLS ...]
    python3 -I tools/listener/bank_trace.py copies HEARD TEXT UNITS COPIES [COPIES ...]

An exterior observer's reads; nothing here enters the machine. TEXT is GSM8K problems separated by a
blank line, each a question line and its answer. A problem is named when its question's first word
(a run of letters) is capitalised and HEARD holds that word capitalised more often than in lower
case: the heard text's own reading of a proper name, with no list of names.

- `requests`: for each named problem, one request `p f`: the read at the answer's first byte `p`,
  and a window from the problem's first byte `f`, so the trace's window holds every cell of the
  question.
- `share`: for each request read, where its largest address `|a|²` falls: on the name's cell at the
  question's opening (the class holding byte `f`), on a cell holding a later occurrence of the name
  in the question, on the read's own cell, on another cell of the question, or in an earlier
  problem; whether the largest share `|a|² ‖w‖²` falls on the name; the opening name cell's rank
  among the window's addresses, beside the chance a uniform rank would give, `1/n` over the
  window's `n` cells; where inside the question the largest address falls, by quarter of the way
  from the name's cell to the read's; split by whether the answer opens with the name. Then the
  bytes of the cells the largest address falls on inside the problem, most frequent first (a
  cell's bytes run to the next cell with a nonzero address).
- `role`: for each CELLS file (`read-tower-held-cells` output with ranks), at every named problem
  whose answer opens with the name, whether the face at the answer's opening gives the answer's
  first unit the largest mass (rank 0: no class carries more), and its code; a problem whose
  opening is a chunk's first class (coded by no cell) is counted as skipped. Then how many classes
  carry more than the first unit, in bands, and, for every file after the first, how many of the
  answers the file before gave the largest mass it keeps and how many it gains. TEXT may be the
  heard text itself, which reads the role on seen problems.
- `copies`: for each COPIES file (`read-tower-clock-cells` output at the `requests` reads), at
  every named problem whose answer opens with the name, read: the margin of the answer's first unit
  over its strongest rival on the face (the logits' difference, in bits), the copies' raise on the
  first unit and on the rival (each the sum of the raises of the clocks holding it), and the readout's
  own margin, the margin less the first unit's raise and plus the rival's. Then which clocks hold
  the first unit and the rival, the rivals' pieces where the rival carries more (UNITS is the founding
  list, `founded-units-v1`), and, for every file after the first, the mean change of each part over
  the answers the file before gave the largest mass, split by whether this file keeps it.
- `held`: for two CELLS files over the same TEXT (a twin's, then a clocked tower's), every coded
  cell set beside the arrival the clock holds there (the cell after the last cell whose bytes are
  the clock's class): where the cell's bytes repeat the held arrival's, and elsewhere by how many
  cells have passed since the reset. The class is the optional fourth argument, written as
  `found-tower-clock` prints its `piece=` (a quoted string with its escapes); a blank line when
  it is absent. For each part: its cells, how many the face gives the
  largest mass in each file, and the code each file gives it, whole and as the second file's
  difference from the first, in bits.
"""
import ast
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
    landed = collections.Counter()
    for start, opening, word, opens in named(heard, text):
        if opening not in reads:
            continue
        read_place, name_place, nonzero, largest, largest_share = reads[opening]
        window = rows[opening]
        present = max((r[0] for r in window), default=None)
        # A cell's bytes run to the next kept cell (a cell with a zero address joins the one before).
        places = sorted({r[0] for r in window} | {name_place})
        ends = dict(zip(places, places[1:] + [read_place]))
        later = [m.start() for m in re.compile(rb"\b" + word + rb"\b").finditer(text, start + len(word), opening)]

        def holds_name(c):
            e = ends.get(c, c + 1)
            return any(c < o + len(word) and o < e for o in later)

        if largest == name_place:
            where = "the name at the question's opening"
        elif largest >= name_place and holds_name(largest):
            where = "the name later in the question"
        elif largest == present:
            where = "the read's own cell"
        elif largest >= name_place:
            where = "another cell of the question"
        else:
            where = "an earlier problem"
        if largest >= name_place:
            landed[text[largest:ends.get(largest, largest + 1)]] += 1
        for kind in ("all", "answer opens with the name" if opens else "answer opens otherwise"):
            t = tally[kind]
            t["reads"] += 1
            t[f"largest address on {where}"] += 1
            if largest >= name_place:
                quarter = min(4 * (largest - name_place) // (read_place - name_place), 3) + 1
                t[f"largest address inside the question, quarter {quarter} of 4"] += 1
            share_on = "the name" if largest_share == name_place or (largest_share >= name_place and holds_name(largest_share)) else "elsewhere"
            t[f"largest share on {share_on}"] += 1
            order = [r[0] for r in sorted(window, key=lambda r: (-r[1], -r[0]))]
            cells = len({r[0] for r in window} | {name_place})
            # A cell with no row has a zero address: it ranks last.
            ranks[kind].append((1 + order.index(name_place) if name_place in order else cells, cells))
    for kind in ("all", "answer opens with the name", "answer opens otherwise"):
        t, r = tally[kind], ranks[kind]
        if not t["reads"]:
            continue
        n = t["reads"]
        print(f"{kind}: {n} reads")
        for key in sorted(k for k in t if k != "reads"):
            print(f"  {key:<52} {t[key]:6d}  {t[key] / n:.4f}")
        mean_rank = sum(a for a, _ in r) / len(r)
        chance = sum(1 / b for _, b in r) / len(r)
        cells = sum(b for _, b in r) / len(r)
        first = sum(a == 1 for a, _ in r) / len(r)
        print(f"  the opening name's rank among the window's addresses: mean {mean_rank:.2f} of {cells:.1f} cells; first {first:.4f}; a uniform rank would be first {chance:.4f}")
    print("the cells the largest address falls on inside the problem, most frequent first:")
    for cell, n in landed.most_common(16):
        print(f"  {n:5d}  {cell!r}")


def role(heard, text, paths):
    asked = [opening for _, opening, _, opens in named(heard, text) if opens]
    before = None
    for path in paths:
        cells = {}
        for line in open(path):
            place, code, _, rank = line.rstrip("\n").split("\t")
            cells[int(place)] = (int(code), int(rank))
        read = {p: cells[p] for p in asked if p in cells}
        first = {p for p, (_, rank) in read.items() if rank == 0}
        bits = sum(code for code, _ in read.values()) / (1 << 20) / len(read) if read else float("nan")
        print(f"{path}: {len(asked)} named answers opening with the name, {len(read)} read, {len(asked) - len(read)} skipped; "
              f"the first unit has the largest mass in {len(first)}; its mean code {bits:.3f} bits")
        # How far the first unit stands from the largest mass: the classes carrying more than it.
        bands = ((0, 0), (1, 1), (2, 4), (5, 15), (16, None))
        counts = [sum(lo <= rank and (hi is None or rank <= hi) for _, rank in read.values()) for lo, hi in bands]
        print("  classes above the first unit: " + ", ".join(
            f"{lo if lo == hi else f'{lo}+' if hi is None else f'{lo}-{hi}'} in {n}" for (lo, hi), n in zip(bands, counts)))
        if before is not None:
            print(f"  beside the file before: keeps the largest mass in {len(first & before)} of its {len(before)}, gains it in {len(first - before)}")
        before = first


def pieces_of(path):
    """The units' pieces from a founding list: the 256 bytes, then each merge's two pieces joined."""
    lines = open(path).read().split("\n")
    head = lines[0].split(" ")
    if len(head) != 2 or head[0] != "founded-units-v1":
        raise SystemExit("not a founding list")
    pieces = [bytes([b]) for b in range(256)]
    for line in lines[1:1 + int(head[1])]:
        a, b = (int(x) for x in line.split(" "))
        pieces.append(pieces[a] + pieces[b])
    return pieces


def copies(heard, text, pieces, paths):
    asked = [opening for _, opening, _, opens in named(heard, text) if opens]
    grain, raise_grain = 1 << 20, 1 << 16
    before = None
    for path in paths:
        rows = {}
        for line in open(path):
            k = line.rstrip("\n").split("\t")
            place, unit, code, rank, rival, rival_code = (int(x) for x in k[:6])
            clocks = [(int(h), None if r == "-" else int(r)) for h, r in zip(k[6::2], k[7::2])]
            rows[place] = (unit, code, rank, rival, rival_code, clocks)
        parts = {}
        for p in asked:
            if p not in rows:
                continue
            unit, code, rank, rival, rival_code, clocks = rows[p]
            on_unit = sum(r for h, r in clocks if h == unit and r is not None) / raise_grain
            on_rival = sum(r for h, r in clocks if h == rival and r is not None) / raise_grain
            margin = (rival_code - code) / grain
            parts[p] = (rank == 0, margin, on_unit, on_rival, margin - on_unit + on_rival,
                        tuple(c for c, (h, _) in enumerate(clocks) if h == unit),
                        tuple(c for c, (h, _) in enumerate(clocks) if h == rival), rival)
        n = len(parts)
        first = {p for p, v in parts.items() if v[0]}
        mean = lambda i, ps: sum(parts[p][i] for p in ps) / len(ps) if ps else float("nan")
        print(f"{path}: {len(asked)} named answers opening with the name, {n} read; the first unit has the largest mass in {len(first)}")
        print(f"  means over the {n}: margin over the rival {mean(1, parts):+.3f} bits = readout {mean(4, parts):+.3f}"
              f" + raise on the first unit {mean(2, parts):+.3f} − raise on the rival {mean(3, parts):+.3f}")
        holds = collections.Counter(v[5] for v in parts.values())
        rivals = collections.Counter(v[6] for v in parts.values())
        print("  clocks holding the first unit: " + ", ".join(f"{list(k) or 'none'} in {m}" for k, m in holds.most_common()))
        print("  clocks holding the rival: " + ", ".join(f"{list(k) or 'none'} in {m}" for k, m in rivals.most_common()))
        above = collections.Counter(pieces[v[7]] for v in parts.values() if not v[0])
        print("  the rival where it carries more, most frequent first: " + ", ".join(f"{piece!r} {m}" for piece, m in above.most_common(12)))
        if before is not None:
            for kind, ps in (("kept", before[1] & first), ("lost", before[1] - first)):
                ps = [p for p in ps if p in parts and p in before[0]]
                if ps:
                    change = lambda i: sum(parts[p][i] - before[0][p][i] for p in ps) / len(ps)
                    print(f"  beside the file before, over the {len(ps)} it {kind}: margin {change(1):+.3f} = readout {change(4):+.3f}"
                          f" + raise on the first unit {change(2):+.3f} − raise on the rival {change(3):+.3f}")
        before = (parts, first)


def cells_of(path):
    cells = {}
    for line in open(path):
        place, code, length, rank = line.rstrip("\n").split("\t")
        cells[int(place)] = (int(code), int(length), int(rank))
    return cells


def class_bytes(printed):
    """A class's bytes from the quoted string `found-tower-clock` prints as its `piece=`."""
    printed = re.sub(r"\\u\{([0-9a-fA-F]+)\}", lambda m: "\\U" + m.group(1).rjust(8, "0"), printed)
    return ast.literal_eval(printed).encode("utf-8")


def held(text, first, second, reset=b"\n\n"):
    a, b = cells_of(first), cells_of(second)
    if a.keys() != b.keys() or any(a[p][1] != b[p][1] for p in a):
        raise SystemExit("the two CELLS files do not code the same cells")
    parts = collections.defaultdict(lambda: [0, 0, 0, 0, 0])
    arrival, since = None, None
    previous = None
    for p in sorted(a):
        piece = text[p:p + a[p][1]]
        if previous == reset:
            arrival, since = piece, 0
            part = "the held arrival itself"
        elif arrival is None:
            part = "before any reset"
        else:
            since += 1
            if piece == arrival:
                part = "repeats the held arrival"
            else:
                part = "elsewhere, " + next(f"{lo}-{hi} cells after the reset" for lo, hi in ((1, 8), (9, 32), (33, 128), (129, 10**9)) if since <= hi)
        r = parts[part]
        r[0] += 1
        r[1] += a[p][2] == 0
        r[2] += b[p][2] == 0
        r[3] += a[p][0]
        r[4] += b[p][0]
        previous = piece
    order = ["before any reset", "the held arrival itself", "repeats the held arrival"] + [f"elsewhere, {lo}-{hi} cells after the reset" for lo, hi in ((1, 8), (9, 32), (33, 128), (129, 10**9))]
    total = [sum(r[i] for r in parts.values()) for i in range(5)]
    print(f"{first} then {second}: {total[0]} cells; the second codes {(total[4] - total[3]) / (1 << 20):+.1f} bits against the first")
    for name in order:
        if name in parts:
            n, fa, fb, ca, cb = parts[name]
            print(f"  {name}: {n} cells; largest mass {fa} then {fb}; code {ca / (1 << 20) / n:.3f} then {cb / (1 << 20) / n:.3f} bits a cell; difference {(cb - ca) / (1 << 20):+.1f} bits")


def main():
    read = lambda p: open(p, "rb").read()
    command, args = (sys.argv[1], sys.argv[2:]) if len(sys.argv) > 1 else ("", [])
    if command == "requests" and len(args) == 3:
        requests(read(args[0]), read(args[1]), args[2])
    elif command == "share" and len(args) == 3:
        share(read(args[0]), read(args[1]), args[2])
    elif command == "role" and len(args) >= 3:
        role(read(args[0]), read(args[1]), args[2:])
    elif command == "copies" and len(args) >= 4:
        copies(read(args[0]), read(args[1]), pieces_of(args[2]), args[3:])
    elif command == "held" and len(args) in (3, 4):
        reset = class_bytes(args[3]) if len(args) == 4 else b"\n\n"
        held(read(args[0]), args[1], args[2], reset)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
