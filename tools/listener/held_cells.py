#!/usr/bin/env python3
"""Where a tower's held-out code goes, read from `read-tower-held-cells` output.

    python3 -I tools/listener/held_cells.py place TRAIN DEV DEV_ROLES CELLS [CELLS ...]
    python3 -I tools/listener/held_cells.py prefix TRAIN DEV DEV_ROLES CELLS
    python3 -I tools/listener/held_cells.py spans TRAIN DEV DEV_ROLES CELLS [CELLS ...]
    python3 -I tools/listener/held_cells.py copy DEV DEV_ROLES CELLS [CELLS ...]

An exterior observer's reads; nothing here enters the machine. A CELLS file has one line a coded
cell: the place of its first byte in DEV, its code on `2^(−20)` bits, and its bytes (one for a byte
tower, a founded unit's length for a units tower). A cell belongs to the class of its first byte,
and a class's reading is its cells' code over their bytes. Every read is of role 0 (the prose of the
mixed Holonics text) except `copy`, which reads a GSM8K held-out text (problems separated by a blank
line; roles: question 0, answer prose 1, answer numbers 2, markup 3). A word is a run of letters.

- `place`: held-out prose bytes by the longest run starting at or before the byte, and holding it,
  that also occurs in TRAIN (`heard_runs.longest_from_each`), in buckets of 0–3, 4–7, 8–11, 12–15,
  16–23 and 24 or more bytes; then by word place: a letter of a word TRAIN holds (heard) or not,
  the word's first letter or a later one, or not a letter.
- `prefix`: a reference for a heard word's later letters (byte towers only): each letter's code
  read from the heard words' prefix counts alone, `−log₂ n(w[:k+1]) / n(w[:k])`, with no context
  beyond the word's own prefix, beside the tower's code for the same letter, by the letter's place
  in its word.
- `spans`: held-out prose cut into spans, each a word with the non-letters after it up to the next
  word; a span is heard when TRAIN holds its word; by word, and by word and length.
- `copy`: an answer's cells (roles 1 and 2) by whether the word holding the cell's first byte is in
  that problem's question (a word or a number, `[A-Za-z]+` or `[0-9]+` with its decimals), by the
  word's kind (capitalised, number, other) and by the cell's place in the word (its first cell or a
  later one); bits a byte and bits a word.
"""
import collections
import math
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import heard_runs  # noqa: E402

G = 1 << 20
LETTERS = re.compile(rb"[A-Za-z]+")
WORD_OR_NUMBER = re.compile(rb"[A-Za-z]+|[0-9]+(?:[.,][0-9]+)*")


def cells_of(path):
    cells = {}
    for line in open(path):
        place, code, length = line.split("\t")
        cells[int(place)] = (int(code), int(length))
    return cells


def name_of(path):
    return "/".join(path.split("/")[-2:])


def reading(cells, places):
    bytes_ = sum(cells[a][1] for a in places)
    return sum(cells[a][0] for a in places) / G / bytes_ if bytes_ else float("nan")


def table(title, klass, reads, names):
    """Each read's classes over its own cells (a byte tower's and a units tower's cells start at
    different places): per class and read, bits a byte, with the cells and bytes read."""
    print(title)
    groups = [collections.defaultdict(list) for _ in reads]
    for g, r in zip(groups, reads):
        for a in r:
            k = klass(a)
            if k is not None:
                g[k].append(a)
    for k in sorted(set().union(*groups)):
        line = f"  {k:<30}"
        for n, r, g in zip(names, reads, groups):
            places = g.get(k, [])
            line += f"  {n}={reading(r, places):.3f} ({len(places)} cells, {sum(r[a][1] for a in places)} B)"
        print(line)


def place(train, dev, roles, paths):
    reads = [cells_of(p) for p in paths]
    names = [name_of(p) for p in paths]
    idx = [i for i, r in enumerate(roles) if r == 0]
    text = bytes(dev[i] for i in idx)
    match = heard_runs.longest_from_each(train, text)
    cover = [0] * len(text)
    for i, length in enumerate(match):
        for j in range(i, i + length):
            cover[j] = max(cover[j], length)
    cover_of = {idx[j]: cover[j] for j in range(len(text))}
    edges = [0, 4, 8, 12, 16, 24]

    def bucket(a):
        if a not in cover_of:
            return None
        c = cover_of[a]
        lo = max(e for e in edges if e <= c)
        hi = edges[edges.index(lo) + 1] - 1 if lo != edges[-1] else None
        return f"cover {lo:02d}-{hi:02d}" if hi is not None else f"cover {lo:02d}-up"

    vocab = set(LETTERS.findall(train))
    word_of = {}
    for m in LETTERS.finditer(dev):
        for j in range(m.start(), m.end()):
            word_of[j] = (m.start(), m.group())

    def word_place(a):
        if a not in cover_of:
            return None
        if a not in word_of:
            return "not a letter"
        s, w = word_of[a]
        return f"{'heard' if w in vocab else 'unheard'} word, {'first letter' if a == s else 'later letter'}"

    table("BY_COVER (the longest heard run holding the cell's first byte)", bucket, reads, names)
    table("BY_WORD_PLACE", word_place, reads, names)


def prefix(train, dev, roles, path):
    cells = cells_of(path)
    if any(n != 1 for _, n in cells.values()):
        raise SystemExit("prefix reads a byte tower's cells only")
    words = collections.Counter(LETTERS.findall(train))
    before = collections.Counter()
    after = collections.Counter()
    for w, n in words.items():
        for k in range(len(w)):
            before[w[:k]] += n
            after[w[:k + 1]] += n
    rows = collections.defaultdict(lambda: [0.0, 0.0, 0])
    for m in LETTERS.finditer(dev):
        w = m.group()
        if roles[m.start()] != 0 or w not in words:
            continue
        for k in range(1, len(w)):
            j = m.start() + k
            if j not in cells:
                continue
            row = rows[min(k, 6)]
            row[0] += cells[j][0] / G
            row[1] += -math.log2(after[w[:k + 1]] / before[w[:k]])
            row[2] += 1
    t, b, n = (sum(r[i] for r in rows.values()) for i in range(3))
    print(f"LATER_LETTERS heard words: {n} letters; tower {t / n:.3f} bits a letter; the heard words' prefix counts alone {b / n:.3f}")
    for k in sorted(rows):
        t, b, n = rows[k]
        print(f"  letter {k + 1 if k < 6 else '7+'} of its word: {n:5d} letters, tower {t / n:.3f}, prefix counts {b / n:.3f}")


def spans(train, dev, roles, paths):
    reads = [cells_of(p) for p in paths]
    names = [name_of(p) for p in paths]
    vocab = set(LETTERS.findall(train))
    words = [m for m in LETTERS.finditer(dev) if roles[m.start()] == 0]
    span_of = {}
    for i, m in enumerate(words):
        end = words[i + 1].start() if i + 1 < len(words) else len(dev)
        for j in range(m.start(), end):
            if roles[j] == 0:
                span_of[j] = i
    for by_length in (False, True):
        def klass(a):
            if a not in span_of:
                return None
            w = words[span_of[a]].group()
            k = "heard word" if w in vocab else "unheard word"
            return k + (f", {len(w)} letters" if len(w) < 8 else ", 8+ letters") if by_length else k
        table("BY_WORD_AND_LENGTH" if by_length else "BY_WORD", klass, reads, names)
        if not by_length:
            for n, r in zip(names, reads):
                for heard in ("heard word", "unheard word"):
                    places = [a for a in r if klass(a) == heard]
                    count = len({span_of[a] for a in places})
                    print(f"  {n} {heard}: {len(places) / count:.2f} cells a word over {count} words")


def copy(dev, roles, paths):
    reads = [cells_of(p) for p in paths]
    names = [name_of(p) for p in paths]
    klass = {}
    for m in re.finditer(rb"(?s).+?(?:\n\n|\Z)", dev):
        s, e = m.start(), m.end()
        question = set(w.group() for w in WORD_OR_NUMBER.finditer(dev, s, e) if roles[w.start()] == 0)
        for w in WORD_OR_NUMBER.finditer(dev, s, e):
            if roles[w.start()] not in (1, 2):
                continue
            t = w.group()
            kind = "number" if t[:1].isdigit() else ("capitalised" if t[:1].isupper() else "other word")
            where = "in question" if t in question else "not in question"
            for j in range(w.start(), w.end()):
                klass[j] = (f"{where}: {kind}", "first cell" if j == w.start() else "later cell", w.start())
    groups = collections.defaultdict(list)
    for a in reads[0]:
        if a in klass and all(a in r for r in reads):
            k = klass[a]
            groups[(k[0], k[1])].append((a, k[2]))
            groups[(k[0], "all cells")].append((a, k[2]))
    for key in sorted(groups):
        items = groups[key]
        places = [a for a, _ in items]
        words = len({w for _, w in items})
        line = f"  {key[0]:<28} {key[1]:<10} cells={len(places):6d} words={words:6d}"
        for n, r in zip(names, reads):
            code = sum(r[a][0] for a in places) / G
            line += f"  {n}={reading(r, places):.3f} b/B {code / words:.2f} b/word"
        print(line)


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    read = lambda p: open(p, "rb").read()
    command, args = sys.argv[1], sys.argv[2:]
    if command == "place" and len(args) >= 4:
        place(read(args[0]), read(args[1]), read(args[2]), args[3:])
    elif command == "prefix" and len(args) == 4:
        prefix(read(args[0]), read(args[1]), read(args[2]), args[3])
    elif command == "spans" and len(args) >= 4:
        spans(read(args[0]), read(args[1]), read(args[2]), args[3:])
    elif command == "copy" and len(args) >= 3:
        copy(read(args[0]), read(args[1]), args[2:])
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
