"""A cause-test foil of the founded units: every founded unit whose bytes hold a decimal digit is
removed, so each digit is read as its own byte unit.

The founded units weld digits to operators and markup differently from one calculation to the next
(`2*` `12` `=` against `24` `*` `3=`). This foil tests whether that welding is why the tower writes
calculations wrong, by training the same recipe on the units with every digit-bearing merge taken
out. It is never the product: a founding rule that names digits is text-specific, and the founding
reads any passage of byte classes (`hnn::units`). Record:
research/records/2026-10-26_THE_SECOND_LAP_WRITES_BACK_225_OF_1572_HEARD_CALCULATIONS_SO_THE_DIGIT_UNITS_ARE_TESTED_AS_THE_CAUSE.md

    python3 -I tools/gsm8k/digit_units.py UNITS OUT

A merge is kept when neither of its units' bytes holds a digit; a kept merge's units are then kept
too, since their bytes are part of its own. The kept merges keep their founding order and are
renumbered in it, so the list reads as `Units::from_text` reads a founding list.
"""

import sys


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    lines = open(sys.argv[1]).read().split("\n")
    head = lines[0].split(" ")
    if len(head) != 2 or head[0] != "founded-units-v1":
        raise SystemExit("not a founding list's text")
    merges = [tuple(map(int, line.split(" "))) for line in lines[1:] if line]
    if len(merges) != int(head[1]):
        raise SystemExit("the founding list's count differs from its merges")
    pieces = [bytes([b]) for b in range(256)]
    renumber = {b: b for b in range(256)}
    kept = []
    for i, (a, b) in enumerate(merges):
        pieces.append(pieces[a] + pieces[b])
        if any(48 <= c <= 57 for c in pieces[256 + i]):
            continue
        renumber[256 + i] = 256 + len(kept)
        kept.append((renumber[a], renumber[b]))
    with open(sys.argv[2], "x") as f:
        f.write(f"founded-units-v1 {len(kept)}\n" + "".join(f"{a} {b}\n" for a, b in kept))
    print(f"DIGIT_UNITS founded={len(merges)} kept={len(kept)} removed={len(merges) - len(kept)}")


if __name__ == "__main__":
    main()
