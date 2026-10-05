#!/usr/bin/env python3
"""The text loop's request / release / truth triples and their copy lengths (the record
`2026-10-05_THE_SAME_PATH_ON_TEXT_KEY_LOCATION_AND_THE_RELEASE_ON_THE_BYTE_CHART.md`).

    python3 triples.py <private out dir> <state> [<state> ...]

Reads what `hnn_prediction executed text` wrote to the private directory (the training passage, each
request, its truth, each state's release and sections) and writes the triples, escaped, to
`<out dir>/triples.txt` (owner-only; private text, never committed). Stdout carries integers only: per
state and request, released or held, the bytes released, and the copy length (`tools/copy_length.py`,
guard 19) of the released bytes against the training passage (the admitted passage) and against the
request itself. A copy length is a receipt, never a control or a grade.

Escaping: valid UTF-8 is shown as its characters; a backslash as `\\\\`; newline, tab and carriage
return as `\\n`, `\\t`, `\\r`; every other control byte and every byte that is not valid UTF-8 as
`\\xNN`; the termination class as `<end>`.
"""

import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
spec = importlib.util.spec_from_file_location("copy_length", os.path.join(ROOT, "tools", "copy_length.py"))
copy_length_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(copy_length_module)
TERMINATION = 256


def escape(data):
    out, i = [], 0
    while i < len(data):
        ch, width = None, 1
        for width in (1, 2, 3, 4):
            try:
                ch = data[i:i + width].decode("utf-8")
                break
            except UnicodeDecodeError:
                ch = None
        if ch is None:
            out.append("\\x%02x" % data[i])
            i += 1
            continue
        i += width
        if ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ch == "\r":
            out.append("\\r")
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append("\\x%02x" % ord(ch))
        else:
            out.append(ch)
    return "".join(out)


def classes_text(classes):
    """A held section's top classes: the bytes escaped, the termination as <end>."""
    pieces, run = [], bytearray()
    for c in classes:
        if c == TERMINATION:
            if run:
                pieces.append(escape(bytes(run)))
                run = bytearray()
            pieces.append("<end>")
        else:
            run.append(c)
    if run:
        pieces.append(escape(bytes(run)))
    return "".join(pieces)


def read(path):
    with open(path, "rb") as handle:
        return handle.read()


def main(argv):
    out, states = argv[1], argv[2:]
    training = os.path.join(out, "training.bin")
    count = len([n for n in os.listdir(out) if re.fullmatch(r"request_\d+\.bin", n)])
    lines = []
    for state in states:
        sections = {}
        with open(os.path.join(out, f"{state}_sections.txt"), encoding="utf-8") as handle:
            for line in handle:
                m = re.match(r"request (\d+): (released|held|refused)(?: \| classes \[([^\]]*)\] \| plural \[([^\]]*)\])?", line)
                if m:
                    classes = [int(x) for x in m.group(3).split(",")] if m.group(3) else []
                    plural = [int(x) for x in m.group(4).split(",")] if m.group(4) else []
                    sections[int(m.group(1))] = (m.group(2), classes, plural)
        lines.append(f"== state {state}")
        for i in range(count):
            request = read(os.path.join(out, f"request_{i}.bin"))
            truth = read(os.path.join(out, f"truth_{i}.bin"))
            release = read(os.path.join(out, f"{state}_{i}.release"))
            decision, classes, plural = sections.get(i, ("missing", [], []))
            against_training = copy_length_module.copy_length(release, [training])["copy_length"]
            against_request = copy_length_module.copy_length(release, [os.path.join(out, f"request_{i}.bin")])["copy_length"]
            print(f"{state} request {i}: {decision}, released bytes {len(release)}, copy length "
                  f"against the training passage {against_training}, against its request {against_request}, "
                  f"plural stations {len(plural)}")
            lines.append(f"-- request {i}")
            lines.append(f"request (last 40 bytes): {escape(request)}")
            if decision == "released":
                lines.append(f"released ({len(release)} bytes): {escape(release)}")
            else:
                lines.append(f"{decision}; top classes per station: {classes_text(classes)}; plural stations {plural}")
            lines.append(f"truth (next 8 bytes):    {escape(truth)}")
            lines.append(f"copy length: against the training passage {against_training}, against its request {against_request}")
    path = os.path.join(out, "triples.txt")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main(sys.argv)
