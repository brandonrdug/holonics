#!/usr/bin/env -S python3 -I
"""The arithmetic world as a slice of a store (the theory thread's Build A of November 16 17:05 UTC; Brandon's direction of 17:00Z: arithmetic
in symbols, a world that answers each problem deterministically, as an interpreter would). A terrain may generate its truth with authored
routines at declared widths, and only its text reaches the machine: the expressions are drawn and evaluated here, at the boundary, by
integer arithmetic, and the field meets only the records.

Usage: arithmetic_world.py OUT KEY TEXT_OCTETS [--records-a-document R] [--held K]
       [--lengths W1,..,W6 --operands W2,W3,W4 --ops W+,W-,W*] [--octaves N]

A record is one line, `EXPR = VALUE`, as written (the most significant digit first, a negative value with its sign): two to four operands,
each of one to six digits drawn uniform in length and in digits (a leading digit nonzero unless the operand is one digit), joined by `+`,
`-` and `*` with a space on each side, every operation below the outermost in parentheses, so the nesting is at most two deep. The draw is
keyed: SHA-256 of `KEY:draw:k` seeds the k-th record, so the slice is the same bytes for the same key.

Training (`DOCS_arithmetic.*`): R (32) records a document, one after another, until the text reaches TEXT_OCTETS. A record whose keyed
held mark falls below one in a thousand is left out of training.
Held (`HELD_arithmetic.*`): K (128) of those held-out records at the met lengths, then K whose operands are each of seven to nine digits
(lengths no training record has), each record one document of its own. `HELD_FORMS_arithmetic.tsv` gives, for each held record of two
operands, the same numbers in three forms for the anchor read: symbols (`a + b =`), words (`a plus b equals`, `minus`, `times`) and a foil
of the same lengths the passage never uses (`plux`, `minux`, `timex`, `eqvals`), with the value.

The weighed draw (the lead, November 16; `--lengths`, `--operands`, `--ops`, given together): the operand lengths one to six, the count
of operands two to four and the operations are drawn with integer weights in place of the uniform draws, under their own draw label, so a
slice drawn without them is the bytes it was. The weights are counts a ruler reads from the store's word problems
(`tools/words_arithmetic_ruler.py`): the arithmetic the word problems hold has numerals of one or two digits at more than four in five,
where the uniform draw gives a third. `--octaves N` cuts the training documents at 1, 2, 4, ... 2^(N-1) records, as many octets an
octave: a record alone is the region its own equation closes in, and the larger documents ask a place to find its operands among other
records' digits. The held records at the met lengths follow the same draw; a store that keeps its earlier held files keeps their
records out of training, since the held mark is keyed by a record's text alone.

The files are corpus_passage.py's: `DOCS_<slice>.bin` the documents' bytes one after another, `DOCS_<slice>.tsv` one row a piece
(`document title_octets text_octets opens closes`; no title, every piece a whole document), `IDS_<slice>.txt` an identifier a document. It
prints the slice's rows for `STORE.tsv` (train and prefix, the same documents, and held) with their SHA-256.
"""
import argparse
import hashlib
import os

OPS = ("+", "-", "*")
WORDS = {"+": "plus", "-": "minus", "*": "times"}
FOILS = {"+": "plux", "-": "minux", "*": "timex"}
SLICE = "arithmetic"
INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"


class Draw:
    """A keyed stream of draws for one record."""

    def __init__(self, key, label):
        self.seed = hashlib.sha256(f"{key}:{label}".encode()).digest()
        self.block = b""
        self.k = 0

    def take(self, n):
        while len(self.block) < n:
            self.block += hashlib.sha256(self.seed + self.k.to_bytes(8, "big")).digest()
            self.k += 1
        out, self.block = self.block[:n], self.block[n:]
        return int.from_bytes(out, "big")


def weighted(d, weights):
    """An index drawn with the given integer weights: a keyed draw of eight octets modulo their sum."""
    u = d.take(8) % sum(weights)
    for i, w in enumerate(weights):
        if u < w:
            return i
        u -= w


def operand(d, low, high, lengths=None):
    length = low + (d.take(1) % (high - low + 1) if lengths is None else weighted(d, lengths))
    first = 0 if length == 1 else 10 ** (length - 1)
    return first + d.take(8) % (10**length - first)


def tree(d, leaves, ops=None):
    """A binary tree of `leaves` operands: a leaf is None, an inner node (op, left, right)."""
    if leaves == 1:
        return None
    left = 1 + d.take(1) % (leaves - 1)
    return (OPS[d.take(1) % 3 if ops is None else weighted(d, ops)], tree(d, left, ops), tree(d, leaves - left, ops))


def fill(node, numbers):
    if node is None:
        return numbers.pop(0)
    op, a, b = node
    return (op, fill(a, numbers), fill(b, numbers))


def value(node):
    if isinstance(node, int):
        return node
    op, a, b = node
    x, y = value(a), value(b)
    return x + y if op == "+" else x - y if op == "-" else x * y


def written(node, root=True):
    if isinstance(node, int):
        return str(node)
    op, a, b = node
    text = f"{written(a, False)} {op} {written(b, False)}"
    return text if root else f"({text})"


def record(key, k, low, high, law=None):
    """The k-th record. `law` (lengths, operands, ops: integer weights) draws a weighed record under its own label, so the uniform draw's
    records stay the bytes they were."""
    if law is None:
        d = Draw(key, f"draw:{low}:{high}:{k}")
        leaves = 2 + d.take(1) % 3
        shape = tree(d, leaves)
        numbers = [operand(d, low, high) for _ in range(leaves)]
    else:
        lengths, operands, ops = law
        d = Draw(key, f"draw:weighed:{low}:{high}:{k}")
        leaves = 2 + weighted(d, operands)
        shape = tree(d, leaves, ops)
        numbers = [operand(d, low, high, lengths) for _ in range(leaves)]
    expr = fill(shape, numbers)
    return expr, f"{written(expr)} = {value(expr)}\n"


def held_mark(key, text):
    return int.from_bytes(hashlib.sha256(f"{key}:held:{text}".encode()).digest()[:4], "big") % 1000 == 0


def write_slice(out, stem, documents):
    """Writes one role's three files; returns (documents, octets, sha256 of the documents' bytes)."""
    h = hashlib.sha256()
    octets = 0
    with open(os.path.join(out, f"{stem}_{SLICE}.bin"), "xb") as b, open(os.path.join(out, f"{stem}_{SLICE}.tsv"), "x") as t, open(os.path.join(out, f"{'HELD_IDS' if stem == 'HELD' else 'IDS'}_{SLICE}.txt"), "x") as ids:
        t.write(INDEX_HEAD)
        for n, (ident, text) in enumerate(documents):
            data = text.encode()
            b.write(data)
            h.update(data)
            octets += len(data)
            t.write(f"{n}\t0\t{len(data)}\t1\t1\n")
            ids.write(f"{ident}\n")
    return octets, h.hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("out")
    p.add_argument("key")
    p.add_argument("text_octets", type=int)
    p.add_argument("--records-a-document", type=int, default=32)
    p.add_argument("--held", type=int, default=128)
    p.add_argument("--lengths", help="six weights, the operand lengths one to six")
    p.add_argument("--operands", help="three weights, two to four operands")
    p.add_argument("--ops", help="three weights: + - *")
    p.add_argument("--octaves", type=int, help="documents of 1, 2, 4, ... records, as many octets an octave")
    a = p.parse_args()
    weights = [a.lengths, a.operands, a.ops]
    if any(weights) and not all(weights):
        raise SystemExit("--lengths, --operands and --ops are given together")
    law = tuple([int(w) for w in v.split(",")] for v in weights) if all(weights) else None
    if law is not None and [len(w) for w in law] != [6, 3, 3]:
        raise SystemExit("--lengths takes six weights, --operands three and --ops three")
    os.makedirs(a.out, exist_ok=True)
    held_met, k, total = [], 0, 0
    train_docs = []

    by_octave = [0] * (a.octaves or 0)

    def training():
        nonlocal k, total
        lines = []
        # [definition; agent-inferred, the lead, November 16] With `--octaves N` a document holds 1, 2, 4, ... or 2^(N-1) records, the next
        # document's octave the one that holds the fewest octets so far (the lowest at a tie), so every octave holds as many octets and no
        # count of records a document is privileged, as the cut draws a stretch's context and run by octaves.
        size = 1 if a.octaves else a.records_a_document
        octave = 0
        while total < a.text_octets:
            expr, line = record(a.key, k, 1, 6, law)
            k += 1
            if held_mark(a.key, line):
                if len(held_met) < a.held:
                    held_met.append((expr, line))
                continue
            lines.append(line)
            total += len(line)
            if len(lines) == size:
                yield (f"arithmetic:{len(train_docs)}", "".join(lines))
                train_docs.append(None)
                if a.octaves:
                    by_octave[octave] += sum(len(x) for x in lines)
                    octave = min(range(a.octaves), key=lambda o: (by_octave[o], o))
                    size = 1 << octave
                lines = []
        if lines:
            yield (f"arithmetic:{len(train_docs)}", "".join(lines))
            train_docs.append(None)

    octets, sha = write_slice(a.out, "DOCS", training())
    kh = k
    while len(held_met) < a.held:
        expr, line = record(a.key, kh, 1, 6, law)
        kh += 1
        if held_mark(a.key, line):
            held_met.append((expr, line))
    held_far = [record(a.key, j, 7, 9) for j in range(a.held)]
    held = [(f"held-met:{n}", line) for n, (_, line) in enumerate(held_met)] + [(f"held-far:{n}", line) for n, (_, line) in enumerate(held_far)]
    held_octets, held_sha = write_slice(a.out, "HELD", held)
    with open(os.path.join(a.out, f"HELD_FORMS_{SLICE}.tsv"), "x") as f:
        f.write("held\tlengths\top\tsymbols\twords\tfoil\tvalue\n")
        for n, (expr, _) in enumerate([e for e in held_met] + [e for e in held_far]):
            if isinstance(expr, tuple) and isinstance(expr[1], int) and isinstance(expr[2], int):
                op, x, y = expr
                lengths = "met" if n < a.held else "far"
                f.write(f"{n}\t{lengths}\t{op}\t{x} {op} {y} =\t{x} {WORDS[op]} {y} equals\t{x} {FOILS[op]} {y} eqvals\t{value(expr)}\n")
    docs = len(train_docs)
    for role in ("train", "prefix"):
        print(f"{role}\t{SLICE}\t-\t0\t{docs}\t{docs}\t{octets}\t{octets}\t{sha}")
    print(f"held\t{SLICE}\t-\t0\t{len(held)}\t{len(held)}\t{held_octets}\t{held_octets}\t{held_sha}")
    print(f"ARITHMETIC_WORLD records_drawn={k} training_documents={docs} training_octets={octets} held={len(held)} held_drawn={kh - k}")
    if a.octaves:
        print("ARITHMETIC_OCTAVES " + " ".join(f"{1 << o}:{n}" for o, n in enumerate(by_octave)))


if __name__ == "__main__":
    main()
