#!/usr/bin/env python3
"""The repository's own text as slices of a store (Brandon, November 22 17:01Z: the mission is composed writes about Holonics theory first,
then logic and code; arithmetic is one probe). The boundary codec of this repository at a commit: its public theory (the guides under
`docs/` and the dated records directly under `research/records/`, Markdown; the receipts beside and under them and the records' index left out) as the slice `theory`, and its
Lean (`lean/**/*.lean`, the build directory left out) as the slice `logic`. A document is one file, its bytes as git holds them at the
commit, with its path as its title (`path\\n` before the text), so a document's place in the tree is read where it opens.

The held cut is by time for the theory, so what is held is what no earlier state could have read: the records dated on or after HELD_FROM
(a `YYYY-MM-DD` prefix of the file name) and no guide. For the logic, the files whose path's SHA-256 falls in the lowest HELD_SHARE
thousandths, a keyed draw over the tree that changes nothing when a file is added elsewhere. Held documents are written as `HELD_<slice>.*`
and left out of the training documents.

Usage: holonics_passage.py OUT COMMIT HELD_FROM HELD_SHARE

Writes corpus_passage.py's files for the slices `theory` and `logic` (`DOCS_*`, `IDS_*`, `HELD_*`, `HELD_IDS_*`) and prints their
`STORE.tsv` rows (train and prefix the whole slice; held the held cut) with their SHA-256. Outside the machine: a boundary codec, and no
text is changed but by the cut.
"""
import hashlib
import os
import subprocess
import sys

INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"


def tracked(commit, prefix, suffix):
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", commit, prefix], capture_output=True, text=True, check=True).stdout
    return sorted(p for p in out.split("\n") if p.endswith(suffix))


def blob(commit, path):
    return subprocess.run(["git", "show", f"{commit}:{path}"], capture_output=True, check=True).stdout


def write_role(out, stem, slice_, documents):
    h = hashlib.sha256()
    octets = n = 0
    ids_name = "HELD_IDS" if stem == "HELD" else "IDS"
    with open(os.path.join(out, f"{stem}_{slice_}.bin"), "xb") as b, open(os.path.join(out, f"{stem}_{slice_}.tsv"), "x") as t, open(os.path.join(out, f"{ids_name}_{slice_}.txt"), "x") as ids:
        t.write(INDEX_HEAD)
        for ident, title, text in documents:
            b.write(title)
            b.write(text)
            h.update(title)
            h.update(text)
            t.write(f"{n}\t{len(title)}\t{len(text)}\t1\t1\n")
            ids.write(f"{ident}\n")
            octets += len(title) + len(text)
            n += 1
    return n, octets, h.hexdigest()


def main():
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    out, commit, held_from, held_share = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    commit = subprocess.run(["git", "rev-parse", commit], capture_output=True, text=True, check=True).stdout.strip()
    os.makedirs(out, exist_ok=True)
    theory = [p for p in tracked(commit, "docs", ".md")] + [p for p in tracked(commit, "research/records", ".md") if p.count("/") == 2 and not p.endswith("/INDEX.md") and not p.endswith("/README.md")]
    logic = [p for p in tracked(commit, "lean", ".lean") if "/.lake/" not in p]

    def held_theory(p):
        name = os.path.basename(p)
        return p.startswith("research/records/") and name[:10] >= held_from

    def held_logic(p):
        return int(hashlib.sha256(p.encode()).hexdigest()[:8], 16) % 1000 < held_share

    for slice_, paths, held in (("theory", theory, held_theory), ("logic", logic, held_logic)):
        docs = [(f"{commit[:12]}:{p}", f"{p}\n".encode(), blob(commit, p)) for p in paths if not held(p)]
        kept = [(f"{commit[:12]}:{p}", f"{p}\n".encode(), blob(commit, p)) for p in paths if held(p)]
        dn, do, ds = write_role(out, "DOCS", slice_, docs)
        hn, ho, hs = write_role(out, "HELD", slice_, kept)
        for role in ("train", "prefix"):
            print(f"{role}\t{slice_}\t0\t0\t{dn}\t{dn}\t{do}\t{do}\t{ds}")
        print(f"held\t{slice_}\t0\t0\t{hn}\t{hn}\t{ho}\t{ho}\t{hs}")
        print(f"HOLONICS_PASSAGE slice={slice_} commit={commit[:12]} documents={dn} octets={do} held={hn} held_octets={ho}", file=sys.stderr)


if __name__ == "__main__":
    main()
