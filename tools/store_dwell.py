#!/usr/bin/env -S python3 -I
"""A store whose named slices stand K times (the lead, November 23: a dwell on the repository's own text, Brandon's 01:13Z note on
reinforcement read as "the same pull comes back"). The cut draws each slice by its places taken against its quota, the slice's store
octets (`holonics_engine::passage::Cut::next`), so a slice held K times is drawn at K times its share of a pass, its documents read in
the same order K times over. Nothing in a document changes and nothing is added: the passage holds the same text more often, as a
reader reads a book again.

Usage: store_dwell.py STORE OUT K SLICE [SLICE ...]

Writes OUT beside STORE: every file of STORE hard-linked but the named slices' training files (`DOCS_<slice>.bin`, `DOCS_<slice>.tsv`,
`IDS_<slice>.txt`), which are written K times over, and `STORE.tsv`, whose `train` and `prefix` rows of the named slices count K times
the documents, pieces and octets of a role that reads the whole slice, with the new file's SHA-256. A role that reads only a prefix of a
named slice is refused (its first pieces would no longer be its own). The held rows and files stand as they were: the held cut is the
same text. Prints each row it changed. Outside the machine: a boundary codec of the passage, and no text is changed.
"""
import hashlib
import os
import sys

HEAD = "role\tslice\tshare\tline_floor\tdocuments\tpieces\ttext_octets\tstore_octets\tsha256"
INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses"


def main():
    if len(sys.argv) < 5:
        sys.exit(__doc__)
    store, out, k, names = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4:]
    if k < 2:
        sys.exit("a dwell of fewer than two")
    rows = open(os.path.join(store, "STORE.tsv")).read().rstrip("\n").split("\n")
    if rows[0] != HEAD:
        sys.exit("a STORE.tsv that does not open with its head")
    os.makedirs(out)
    written = {f"{stem}_{n}.{ext}" for n in names for stem, ext in (("DOCS", "bin"), ("DOCS", "tsv"), ("IDS", "txt"))}
    for f in sorted(os.listdir(store)):
        if f not in written and f != "STORE.tsv":
            os.link(os.path.join(store, f), os.path.join(out, f))
    whole = {}
    for n in names:
        docs = open(os.path.join(store, f"DOCS_{n}.bin"), "rb").read()
        index = open(os.path.join(store, f"DOCS_{n}.tsv")).read().rstrip("\n").split("\n")
        ids = open(os.path.join(store, f"IDS_{n}.txt")).read().rstrip("\n").split("\n")
        if index[0] != INDEX_HEAD:
            sys.exit(f"DOCS_{n}.tsv does not open with its head")
        body = index[1:]
        h = hashlib.sha256()
        with open(os.path.join(out, f"DOCS_{n}.bin"), "xb") as b, open(os.path.join(out, f"DOCS_{n}.tsv"), "x") as t, open(os.path.join(out, f"IDS_{n}.txt"), "x") as i:
            t.write(INDEX_HEAD + "\n")
            for r in range(k):
                b.write(docs)
                h.update(docs)
                for j, line in enumerate(body):
                    w = line.split("\t")
                    t.write("\t".join([str(r * len(body) + j)] + w[1:]) + "\n")
                for ident in ids:
                    i.write(f"{ident}#{r}\n")
        whole[n] = (len(body), len(docs), h.hexdigest())
    new = [HEAD]
    for row in rows[1:]:
        w = row.split("\t")
        if w[1] in names and w[0] in ("train", "prefix"):
            pieces, octets, sha = whole[w[1]]
            if int(w[5]) != pieces or int(w[7]) != octets:
                sys.exit(f"the {w[0]} role reads a prefix of {w[1]} ({w[5]} of {pieces} pieces)")
            w = [w[0], w[1], w[2], w[3], str(k * int(w[4])), str(k * pieces), str(k * int(w[6])), str(k * octets), sha]
            print("STORE_DWELL " + "\t".join(w))
        new.append("\t".join(w))
    with open(os.path.join(out, "STORE.tsv"), "x") as f:
        f.write("\n".join(new) + "\n")


if __name__ == "__main__":
    main()
