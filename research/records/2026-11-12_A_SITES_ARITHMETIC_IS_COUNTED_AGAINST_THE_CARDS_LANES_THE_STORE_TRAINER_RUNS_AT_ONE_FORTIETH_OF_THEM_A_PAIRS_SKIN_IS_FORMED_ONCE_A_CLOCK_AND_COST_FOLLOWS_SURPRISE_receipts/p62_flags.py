"""p62_flags: the receivers' ruler's flags (P62 item 3; a host ruler, numbers only). One thread, no card.

usage: python3 -I p62_flags.py SITE_RULER_DIR STORE EXPORT_DIR COUNT_MB OUT_FLAGS
The count reader of two octets back (site_ruler.py's Witten-Bell Reader) counts the first COUNT_MB million octets of each slice's training
documents (the store's DOCS_<slice>, a document a region, its title then its text); each exported held stretch is read by it and its
landmarks at a section of 8 bits (the claim, site_ruler's law G) are flagged, one flag a place; a place past the stretch's octets (a true
end's voids) is flagged 0. Output: one line a stretch, `use slice a b bits`.
"""
import math
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, sys.argv[1])
import site_ruler as sr  # noqa: E402

store, export, count_mb, out = sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
SIGMA = 8.0 * math.log(2.0)
rows = []
with open(export + "/passages.tsv") as f:
    head = f.readline().rstrip("\n").split("\t")
    for line in f:
        rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))
data = np.fromfile(export + "/passages.bin", dtype=np.uint8)
by_slice = defaultdict(list)
for r in rows:
    by_slice[r["slice"]].append(r)
with open(out, "w") as fo:
    fo.write("use\tslice\ta\tb\tbits\n")
    for name, rs in by_slice.items():
        regions, used = [], 0
        bin_ = np.memmap(f"{store}/DOCS_{name}.bin", dtype=np.uint8, mode="r")
        at = 0
        with open(f"{store}/DOCS_{name}.tsv") as f:
            f.readline()
            for line in f:
                w = line.split("\t")
                n = int(w[1]) + int(w[2])
                if n:
                    regions.append(np.asarray(bin_[at:at + n], dtype=np.int64))
                at += n
                used += n
                if used >= count_mb * 1_000_000:
                    break
        reader = sr.Reader(regions, 256)
        held = [np.asarray(data[int(r["offset"]):int(r["offset"]) + int(r["octets"])], dtype=np.int64) for r in rs]
        codes = reader.codes(held)
        flagged = places = 0
        for r, c in zip(rs, codes):
            sites = sr.claim(c, SIGMA)[0] if len(c) else np.zeros(0, dtype=np.int64)
            bits = np.zeros(int(r["places"]), dtype=np.uint8)
            bits[sites] = 1
            flagged += int(bits.sum())
            places += len(bits)
            fo.write("%s\t%s\t%s\t%s\t%s\n" % (r["use"], name, r["a"], r["b"], "".join("1" if b else "0" for b in bits)))
        allc = np.concatenate([c for c in codes if len(c)])
        print("FLAGS slice=%s count_octets=%d stretches=%d places=%d flagged=%d share=%.4f news_a_place=%.4f" % (name, used, len(rs), places, flagged, flagged / max(places, 1), float(allc.mean())))
