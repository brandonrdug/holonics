"""Fit the pinned F1 finite byte-word dictionary on choosing cells only.

The dictionary and exact integer weights remain owner-only. Validation cells are never opened.
Stdout contains counts, the charged description length and hashes, never any source text.

    HOLONICS_ROOT=<checkout with private cuts> python3 f1_dictionary.py
"""

import collections
import hashlib
import json
import os
import struct
import sys
from array import array

from standing_cut import OUT_DIR, private_directory, private_write

NAME = "f1-word-dictionary.json"
PAIRS = 16


def gamma_count(count):
    """Elias-gamma length of the positive integer count + 1."""
    assert count >= 0
    return 2 * (count + 1).bit_length() - 1


def main():
    if sys.argv[1:]:
        sys.exit(__doc__)
    prefix = os.path.join(OUT_DIR, "curated-f1-choosing-cut")
    with open(prefix + ".json", "rb") as handle:
        manifest = json.load(handle)
    with open(prefix + ".bin", "rb") as handle:
        raw = handle.read()
    assert hashlib.sha256(raw).hexdigest() == manifest["cut_sha256"]
    cells = array("H")
    cells.frombytes(raw)
    if sys.byteorder != "little":
        cells.byteswap()
    assert len(cells) == manifest["cells"]

    singles = [0] * 256
    pairs = collections.Counter()
    previous = None
    letters = 0
    for cell in cells:
        if cell >= 256:
            assert cell < manifest["alphabet"]
            previous = None
            letters += 1
        else:
            singles[cell] += 1
            if previous is not None:
                pairs[bytes((previous, cell))] += 1
            previous = cell
    assert letters > 0 and len(pairs) >= PAIRS
    chosen = [pair for pair, _ in sorted(pairs.items(), key=lambda item: (-item[1], item[0]))[:PAIRS]]
    bytes_count = sum(singles)
    closes = letters - 1
    counts = singles + [pairs[pair] for pair in chosen]
    weights = [count + 1 for count in counts]
    description_bits = PAIRS * 16 + 1 + sum(map(gamma_count, counts)) + gamma_count(bytes_count) + gamma_count(closes)
    receipt = {
        "schema": "holonics.f1-word-dictionary.v1",
        "cut_sha256": manifest["cut_sha256"],
        "words_hex": [bytes((byte,)).hex() for byte in range(256)] + [pair.hex() for pair in chosen],
        "counts": counts,
        "weights": weights,
        "stop_numerator": closes + 1,
        "stop_denominator": closes + bytes_count + 2,
        "description_bits": description_bits,
        "byte_cells": bytes_count,
        "section_letters": letters,
    }
    private_directory()
    packed = json.dumps(receipt, separators=(",", ":"), sort_keys=True).encode()
    private_write(NAME, packed)
    binary = bytearray(struct.pack("<IQQQ", len(weights), closes + 1,
                                   closes + bytes_count + 2, description_bits))
    for word_hex, weight in zip(receipt["words_hex"], weights):
        word = bytes.fromhex(word_hex)
        binary.extend(struct.pack("<HQ", len(word), weight))
        binary.extend(word)
    private_write("f1-word-dictionary.bin", bytes(binary))
    print(json.dumps({"schema": receipt["schema"], "words": len(weights),
                      "byte_cells": bytes_count, "section_letters": letters,
                      "description_bits": description_bits,
                      "dictionary_sha256": hashlib.sha256(packed).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
