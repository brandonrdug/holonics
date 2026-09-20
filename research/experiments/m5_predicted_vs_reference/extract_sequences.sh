#!/usr/bin/env bash
# The two M5 sequences, taken from the authenticated mmCIF files' own `_atom_site` rows rather than
# retyped. Prints one FASTA record per chain, with the chain's residue count in the header comment.
# Usage: extract_sequences.sh <M5_STRUCTURE_ROOT>/designed-free-rbx1.cif
set -euo pipefail
python3 - "$@" <<'PY'
import sys, collections
ONE = dict(zip(
    "ALA ARG ASN ASP CYS GLN GLU GLY HIS ILE LEU LYS MET PHE PRO SER THR TRP TYR VAL".split(),
    "ARNDCQEGHILKMFPSTWYV"))
for path in sys.argv[1:]:
    lines = open(path).read().splitlines()
    at = 0
    while at < len(lines):
        if lines[at].strip() != "loop_":
            at += 1; continue
        cursor, header = at + 1, []
        while cursor < len(lines) and lines[cursor].lstrip().startswith("_"):
            header.append(lines[cursor].strip()); cursor += 1
        if not any(name.startswith("_atom_site.") for name in header):
            at = cursor; continue
        column = {name: k for k, name in enumerate(header)}
        chains = collections.OrderedDict()
        while cursor < len(lines):
            line = lines[cursor].strip()
            if line in ("#", "loop_") or line.startswith("_"):
                break
            if line:
                row = line.split()
                assert len(row) == len(header), (path, cursor + 1)
                if row[column["_atom_site.group_PDB"]] == "ATOM" and \
                   row[column["_atom_site.label_atom_id"]] == "CA":
                    chains.setdefault(row[column["_atom_site.label_asym_id"]], []).append(
                        row[column["_atom_site.label_comp_id"]])
            cursor += 1
        for label, monomers in chains.items():
            print(f">{label}|{len(monomers)} monomers|{path}")
            print("".join(ONE.get(m, "X") for m in monomers))
        break
PY
