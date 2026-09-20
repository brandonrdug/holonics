#!/usr/bin/env python3
"""Stage the bound-partner contact support of RBX1, exactly, with no float anywhere.

This script routes around intake defect #52. `physical_intake::mmcif::StructurePresentation`
refuses a deposited mmCIF whose `HETATM` rows carry `label_seq_id .`, because the parser demands
an integer on every `_atom_site` row. The deposited `3DPL.cif` and `7Z8R.cif` both carry `ZN` and
`HOH` HETATM rows, so neither can be read whole by the library today. The M5 intake staged only
the RBX1 chain, which is why that experiment never met the defect; a *partner* chain has to be
staged the same way before the library can see it, and that is all this script does.

It computes no elastic quantity and decides nothing about the response. It returns, exactly:

  * which RBX1 residues (in M5 numbering) carry an alpha carbon within a **declared** CA-CA
    aperture of any partner-chain alpha carbon, in the deposited bound frame;
  * the partner chains it measured against, with their residue counts;
  * the aperture, as an exact rational square.

Every coordinate is read as a `fractions.Fraction` of the depositor's own decimal string. No
`float` is constructed on any path in this file.

Usage:
    python3 stage_partner_contacts.py --root <M5_STRUCTURE_ROOT> --out contact_support.json
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path

# The deposited entries, their RBX1 chain, and the offset that carries a deposited `label_seq_id`
# to the M5 target's own residue index. Both are copied from the M5 experiment's
# `measured_staging.json`, which derived them from the RCSB sequence alignment; nothing is
# re-derived here.
ENTRIES = {
    "3DPL": {
        "rbx1_chain": "B",
        "label_seq_id_to_m5_offset": 2,
        "partner_chains": ["A"],
        "partner_named": "cullin-5",
        "method": "X-ray, 2.6 A",
    },
    "7Z8R": {
        "rbx1_chain": "C",
        "label_seq_id_to_m5_offset": 2,
        "partner_chains": ["A", "B"],
        "partner_named": "CUL1 and CAND1",
        "method": "cryo-EM, 2.7 A",
    },
}

REPRESENTATIVE = "CA"


def atom_site_rows(text):
    """The `_atom_site` loop's headers and rows, whitespace-tokenised like the library's reader."""
    lines = text.splitlines()
    headers = None
    rows = []
    at = 0
    while at < len(lines):
        line = lines[at].strip()
        if line == "loop_":
            probe = at + 1
            block = []
            while probe < len(lines) and lines[probe].strip().startswith("_atom_site."):
                block.append(lines[probe].strip())
                probe += 1
            if block:
                headers = block
                at = probe
                while at < len(lines):
                    row = lines[at].strip()
                    if row.startswith("#") or row.startswith("loop_") or row.startswith("_"):
                        break
                    if row:
                        rows.append(row.split())
                    at += 1
                break
        at += 1
    if headers is None:
        raise SystemExit("no _atom_site loop")
    return headers, rows


def exact(token):
    """The depositor's decimal string as an exact rational. `Fraction(str)` is exact by decimal."""
    return Fraction(token)


def alpha_carbons(headers, rows, chain):
    """`{label_seq_id: (x, y, z)}` for one chain's alpha carbons, ATOM rows with an integer id."""
    index = {name: at for at, name in enumerate(headers)}
    atom = index["_atom_site.label_atom_id"]
    asym = index["_atom_site.label_asym_id"]
    seq = index["_atom_site.label_seq_id"]
    group = index["_atom_site.group_PDB"]
    model = index.get("_atom_site.pdbx_PDB_model_num")
    alt = index.get("_atom_site.label_alt_id")
    xs, ys, zs = (
        index["_atom_site.Cartn_x"],
        index["_atom_site.Cartn_y"],
        index["_atom_site.Cartn_z"],
    )
    places = {}
    dropped_alternate = 0
    for row in rows:
        if row[group] != "ATOM":
            continue
        if model is not None and row[model] != "1":
            continue
        if row[asym] != chain:
            continue
        if row[atom].strip("'\"") != REPRESENTATIVE:
            continue
        try:
            ordinal = int(row[seq])
        except ValueError:
            # This is exactly the row shape defect #52 refuses. A polymer ATOM row never has it.
            continue
        if ordinal in places:
            if alt is not None and row[alt] not in (".", "?"):
                dropped_alternate += 1
                continue
            raise SystemExit(f"chain {chain} residue {ordinal} has two unlabelled alpha carbons")
        places[ordinal] = (exact(row[xs]), exact(row[ys]), exact(row[zs]))
    return places, dropped_alternate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, help="directory holding 3DPL.cif and 7Z8R.cif")
    parser.add_argument("--out", required=True)
    parser.add_argument(
        "--aperture-angstrom",
        default="10",
        help="declared CA-CA inter-chain contact aperture, an exact decimal",
    )
    arguments = parser.parse_args()

    aperture = Fraction(arguments.aperture_angstrom)
    aperture_square = aperture * aperture
    root = Path(arguments.root)

    staged = {
        "schema": "holonics.conditioned-rbx1-static-response.contact-support.v1",
        "what_this_is": (
            "the bound-partner contact support of RBX1, read from the deposited bound frames. "
            "It supplies the SUPPORT of the forcing map B and nothing else: no direction, no "
            "magnitude and no displacement is taken from these files."
        ),
        "declared_aperture_angstrom": str(aperture),
        "declared_aperture_square_angstrom_squared": str(aperture_square),
        "aperture_is_alpha_carbon_to_alpha_carbon": True,
        "arithmetic": "python fractions.Fraction over the depositor's own decimal strings; no float",
        "intake_defect_52": (
            "physical_intake::mmcif refuses these deposited files whole: their HETATM ZN and HOH "
            "rows carry `label_seq_id .` and the parser requires an integer on every row. This "
            "script is the route-around and reads only ATOM rows."
        ),
        "entries": {},
    }

    for entry, declaration in ENTRIES.items():
        path = root / f"{entry}.cif"
        headers, rows = atom_site_rows(path.read_text())
        rbx1, rbx1_dropped = alpha_carbons(headers, rows, declaration["rbx1_chain"])
        offset = declaration["label_seq_id_to_m5_offset"]

        partner_places = []
        partner_counts = {}
        for chain in declaration["partner_chains"]:
            places, _ = alpha_carbons(headers, rows, chain)
            partner_counts[chain] = len(places)
            partner_places.extend(places.values())

        contacts = {}
        for ordinal, (x, y, z) in sorted(rbx1.items()):
            nearest_square = None
            for px, py, pz in partner_places:
                quadrance = (x - px) ** 2 + (y - py) ** 2 + (z - pz) ** 2
                if nearest_square is None or quadrance < nearest_square:
                    nearest_square = quadrance
            if nearest_square is not None and nearest_square <= aperture_square:
                contacts[ordinal + offset] = str(nearest_square)

        staged["entries"][entry] = {
            "method": declaration["method"],
            "rbx1_chain": declaration["rbx1_chain"],
            "partner_chains": declaration["partner_chains"],
            "partner_named": declaration["partner_named"],
            "partner_alpha_carbons": partner_counts,
            "rbx1_alpha_carbons": len(rbx1),
            "rbx1_alternate_rows_dropped": rbx1_dropped,
            "label_seq_id_to_m5_offset": offset,
            "m5_residues_in_contact": sorted(contacts),
            "nearest_partner_quadrance_by_m5_residue": contacts,
        }

    Path(arguments.out).write_text(json.dumps(staged, indent=1) + "\n")
    for entry, reading in staged["entries"].items():
        print(
            entry,
            reading["partner_named"],
            "contacts:",
            len(reading["m5_residues_in_contact"]),
            reading["m5_residues_in_contact"],
        )


if __name__ == "__main__":
    main()
