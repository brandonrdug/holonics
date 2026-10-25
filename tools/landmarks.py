"""Write a landmark stream for a text: one byte per byte of the text, 1 where a reading looks and 0
elsewhere (`found-tower-ring`'s MARKS).

A landmark is received material at the exterior boundary. It says where to look, never what to
find: it is read from the text's shape (where a line's `=` stands and which operation comes before
it), never from a value the text holds or from whether a line is true, and no value of the text
reaches the founding through it. Whoever marks a text, a person or a machine that has learned
more than its first markers, hands over where to look; the exchange is communication.

  after-sum TEXT OUT    every cell from a line's `=` to its last byte, on the lines with a `+`
                        before their `=`
  sum-units TEXT OUT    on each line of the shape `digits+digits=digits`, the cell that codes the
                        result's units (it has heard the byte before them; `tower_modes.py`'s U)

OUT is written create-new.

usage: python3 -I landmarks.py after-sum|sum-units TEXT OUT
"""
import re
import sys

SUM = re.compile(rb"^\d+\+\d+=\d+$")


def after_sum(text):
    marks, start = bytearray(len(text)), 0
    for line in text.split(b"\n"):
        e = line.find(b"=")
        if e >= 0 and b"+" in line[:e]:
            marks[start + e:start + len(line)] = b"\x01" * (len(line) - e)
        start += len(line) + 1
    return marks


def sum_units(text):
    marks, start = bytearray(len(text)), 0
    for line in text.split(b"\n"):
        if SUM.match(line):
            marks[start + len(line) - 2] = 1
        start += len(line) + 1
    return marks


def main():
    if len(sys.argv) != 4 or sys.argv[1] not in ("after-sum", "sum-units"):
        raise SystemExit(__doc__.rsplit("usage: ", 1)[1])
    text = open(sys.argv[2], "rb").read()
    marks = after_sum(text) if sys.argv[1] == "after-sum" else sum_units(text)
    with open(sys.argv[3], "xb") as f:
        f.write(bytes(marks))
    print(f"{sys.argv[1]}: {sum(marks)} of {len(text)} cells marked")


if __name__ == "__main__":
    main()
