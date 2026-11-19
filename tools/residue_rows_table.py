#!/usr/bin/env -S python3 -I
"""Rows for a ruler of the circles' residue (the lead, November 19; the frontier record §23): windows of a slice's text as
`read-strand-states` rows (`label<TAB>known text<TAB>next symbol`), the fitting half from the training documents past the first
SKIP octets (a count fitted on the first SKIP octets reads the same held windows apart from them) and the reading half from the held
documents. A window is kept whole only where its octets all stand in the codec's used set, it holds no tab, and it is whole UTF-8.
Usage: residue_rows_table.py STORE CODEC SLICES FIT_WINDOWS READ_WINDOWS LENGTH SKIP OUT_FIT OUT_READ"""
import sys
store, codec, slices, nfit, nread, length, skip, out_fit, out_read = sys.argv[1:10]
nfit, nread, length, skip = int(nfit), int(nread), int(length), int(skip)
used = set(int(w) for w in open(codec).read().split("\n")[1].split(" "))
def windows(path, start, count):
    data = open(path, "rb").read()
    out, at = [], start
    stride = max(length, (len(data) - start) // max(count * 3, 1))
    while len(out) < count and at + length < len(data):
        w = data[at:at + length]
        if all(b in used for b in w) and b"\t" not in w:
            try:
                t = w.decode("utf-8")
                out.append(t)
            except UnicodeDecodeError:
                pass
        at += stride
    return out
for path_kind, out, count, start in (("DOCS", out_fit, nfit, skip), ("HELD", out_read, nread, 0)):
    with open(out, "w") as o:
        for sl in slices.split(","):
            for i, t in enumerate(windows(f"{store}/{path_kind}_{sl}.bin", start, count)):
                known, nxt = t[:-1], t[-1]
                esc = lambda x: x.replace(chr(10), chr(92) + "n")
                o.write(f"{sl}:{i}:0\t{esc(known)}\t{esc(nxt)}\n")
