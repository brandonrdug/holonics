#!/usr/bin/env python3
"""Rulers on a write from held prompts (P49 item 5 of November 12): a host script, numbers only out; floats here are a ruler's.

  python3 -I write_rulers.py OUT STORE

OUT is a `write-store` directory (each problem's `SLICE_NN.prompt`, `.written` and `.reference`, raw bytes); STORE the documents store
(`tools/corpus_passage.py`). By slice, over the slice's writes, each ruler is read on three texts: the written runs, the reference
continuations (the held pieces' next places; a reference is one specimen), and a foil of as many bytes as each written run, drawn
independently from the slice's held byte counts (FOIL_SEED, a constant of this script, never the key):

  utf8      the share of bytes standing in well-formed UTF-8 sequences (RFC 3629: no overlong form, no surrogate, nothing past U+10FFFF);
  balance   the letters' balance: the divergence in nats of the text's byte counts from the slice's held file's, one half added to each of
            the 256 counts on both sides (on the held side so that a byte the held file never holds keeps the divergence finite);
  words     maximal runs of three or more ASCII letters, lowercased: their count and the share of them found among such words of the slice's
            training file's first WORD_EXTENT bytes (the vocabulary's size printed; a ruler's own extent, no part of the machine);
  match     the share of the reference's places where the text's byte equals the reference's at the same place (a place past a shorter
            text counts as unequal).
"""
import os
import re
import sys
from collections import Counter
from math import log

SLICES = ("code", "web", "science", "books", "wikidata")
FOIL_SEED = 0x5EED_F011
WORD_EXTENT = 100_000_000
WORD = re.compile(rb"[A-Za-z]{3,}")


def mix(seed, counter):
    z = (seed + counter * 0x9E3779B97F4A7C15) & ((1 << 64) - 1)
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & ((1 << 64) - 1)
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & ((1 << 64) - 1)
    return z ^ (z >> 31)


def utf8_valid_bytes(b):
    """The bytes of `b` that stand in well-formed UTF-8 sequences, read greedily from the front."""
    i, good = 0, 0
    while i < len(b):
        c = b[i]
        if c < 0x80:
            good, i = good + 1, i + 1
            continue
        if 0xC2 <= c <= 0xDF:
            n, lo, hi = 2, 0x80, 0xBF
        elif c == 0xE0:
            n, lo, hi = 3, 0xA0, 0xBF
        elif 0xE1 <= c <= 0xEC or 0xEE <= c <= 0xEF:
            n, lo, hi = 3, 0x80, 0xBF
        elif c == 0xED:
            n, lo, hi = 3, 0x80, 0x9F
        elif c == 0xF0:
            n, lo, hi = 4, 0x90, 0xBF
        elif 0xF1 <= c <= 0xF3:
            n, lo, hi = 4, 0x80, 0xBF
        elif c == 0xF4:
            n, lo, hi = 4, 0x80, 0x8F
        else:
            i += 1
            continue
        seq = b[i:i + n]
        if len(seq) == n and lo <= seq[1] <= hi and all(0x80 <= x <= 0xBF for x in seq[2:]):
            good, i = good + n, i + n
        else:
            i += 1
    return good


def counts_of(path):
    c = [0] * 256
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 24), b""):
            for k, v in Counter(block).items():
                c[k] += v
    return c


def balance(text, held):
    t = [0.5] * 256
    for k, v in Counter(text).items():
        t[k] += v
    h = [x + 0.5 for x in held]
    st, sh = sum(t), sum(h)
    return sum((a / st) * log((a / st) / (b / sh)) for a, b in zip(t, h))


def foil(length, held, draw):
    """`length` bytes drawn independently from the held counts (an integer draw against the cumulative counts)."""
    total = sum(held)
    cum, acc = [], 0
    for v in held:
        acc += v
        cum.append(acc)
    out = bytearray()
    for j in range(length):
        u = mix(FOIL_SEED, draw + j) % total
        lo, hi = 0, 255
        while lo < hi:
            mid = (lo + hi) // 2
            if cum[mid] > u:
                hi = mid
            else:
                lo = mid + 1
        out.append(lo)
    return bytes(out)


def vocabulary(path):
    with open(path, "rb") as f:
        data = f.read(WORD_EXTENT)
    return {w.lower() for w in WORD.findall(data)}


def main():
    out, store = sys.argv[1], sys.argv[2]
    names = sorted({f.rsplit("_", 1)[0] for f in os.listdir(out) if f.endswith(".written")}, key=lambda n: SLICES.index(n) if n in SLICES else 99)
    print("RULERS columns: slice text writes octets utf8_share balance_nats words words_found_share match_share")
    for name in names:
        stems = sorted(f[: -len(".written")] for f in os.listdir(out) if f.startswith(name + "_") and f.endswith(".written"))
        held = counts_of(os.path.join(store, f"HELD_{name}.bin"))
        vocab = vocabulary(os.path.join(store, f"DOCS_{name}.bin"))
        written = [open(os.path.join(out, s + ".written"), "rb").read() for s in stems]
        refs = [open(os.path.join(out, s + ".reference"), "rb").read() for s in stems]
        foils = [foil(len(w), held, (k + 1) << 32) for k, w in enumerate(written)]
        print(f"RULERS_VOCABULARY slice={name} extent={WORD_EXTENT} words={len(vocab)}")
        for label, texts in (("written", written), ("reference", refs), ("foil", foils)):
            joined = b"".join(texts)
            words = [w.lower() for t in texts for w in WORD.findall(t)]
            found = sum(1 for w in words if w in vocab)
            places = sum(len(r) for r in refs)
            matches = sum(sum(1 for j in range(min(len(t), len(r))) if t[j] == r[j]) for t, r in zip(texts, refs))
            utf8 = utf8_valid_bytes(joined) / len(joined) if joined else 0.0
            print(f"RULERS slice={name} text={label} writes={len(texts)} octets={len(joined)} utf8_share={utf8:.4f} balance_nats={balance(joined, held):.4f} "
                  f"words={len(words)} words_found_share={(found / len(words)) if words else 0.0:.4f} match_share={matches / places if places else 0.0:.4f}")


if __name__ == "__main__":
    main()
