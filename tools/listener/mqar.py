#!/usr/bin/env python3
"""The MQAR terrain as a class passage and its mark file, for the tower's sectioned trainer.

    python3 tools/listener/mqar.py FIRST COUNT CLASSES_OUT MARKS_OUT

writes passages FIRST .. FIRST+COUNT-1 of the binding bank record's generator (receipt F,
`mqar_passage`, imported from the record's receipts, never ported), back to back: each class as a
big-endian u16, and one mark byte a class, 1 at the 16 answer cells of a passage (the odd cells of
its second half: a value that follows its key's second arrival) and 0 elsewhere. Nothing here enters
the tower: the classes are its terrain and the marks say where the exterior compares a face.

Before writing, it recomputes the held-out set's SHA-256 (passages 1,000,000 .. 1,000,999, each
passage's bytes and a zero byte) and refuses unless it is the record's, so the terrain a run reads is
the one fixed before any run. It refuses to write over an existing file.
"""
import hashlib
import importlib.util
import os
import sys

RECORD = "research/records/2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS_receipts/binding_bank.py"
HELD_OUT = (1_000_000, 1_000)
HELD_OUT_SHA = "67212eb0005aebb84d441a32b00567fac94b7d1a825836d7b847dfed1ae2f0d3"
PASSAGE = 64


def generator():
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    spec = importlib.util.spec_from_file_location("binding_bank", os.path.join(root, RECORD))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.mqar_passage


def main():
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    first, count = int(sys.argv[1]), int(sys.argv[2])
    classes_out, marks_out = sys.argv[3], sys.argv[4]
    if count <= 0 or first < 0:
        sys.exit("FIRST must be a passage index and COUNT positive")
    if first < HELD_OUT[0] + HELD_OUT[1] and first + count > HELD_OUT[0] and (first, count) != HELD_OUT:
        sys.exit("a training range must not meet the held-out passages 1,000,000 .. 1,000,999")
    passage = generator()
    h = hashlib.sha256()
    for i in range(HELD_OUT[0], HELD_OUT[0] + HELD_OUT[1]):
        h.update(bytes(passage(i)) + b"\x00")
    if h.hexdigest() != HELD_OUT_SHA:
        sys.exit("the generator's held-out set is not the record's: " + h.hexdigest())
    marks_one = bytes(1 if j >= PASSAGE // 2 and j % 2 == 1 else 0 for j in range(PASSAGE))
    classes, marks = bytearray(), bytearray()
    for i in range(first, first + count):
        cells = passage(i)
        if len(cells) != PASSAGE or any(not 0 <= c < 128 for c in cells):
            sys.exit(f"passage {i} is not 64 classes of 0..127")
        for c in cells:
            classes += c.to_bytes(2, "big")
        marks += marks_one
    for path, data in ((classes_out, classes), (marks_out, marks)):
        with open(path, "xb") as f:
            f.write(data)
        print(f"MQAR_WROTE {os.path.basename(path)} passages={count} from={first} bytes={len(data)} sha256={hashlib.sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
