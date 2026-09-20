#!/usr/bin/env python3
"""Stage measured RBX1 coordinate files from RCSB for the library's existing mmCIF intake.

[definition] This script **decides nothing and computes no geometry**. It does exactly three
things, and records every one of them:

1. It selects, out of a deposited mmCIF's ``_atom_site`` loop, the rows of ONE polymer chain
   (``label_asym_id``) in ONE model (``pdbx_PDB_model_num``), and writes them to a minimal mmCIF
   whose ``_atom_site`` header is the source's own.  **Every coordinate token is copied verbatim**,
   so the library's exact decimal intake reads the depositor's own decimal strings and no float
   ever exists on this path.  The filter is necessary because
   ``physical_intake::mmcif::StructurePresentation::parse`` requires an integer
   ``_atom_site.label_seq_id``, which a non-polymer (``HETATM``) row does not carry, and because
   the parser keys chains by ``label_asym_id`` alone and would therefore merge an NMR ensemble's
   twenty models into one chain.
2. It aligns the chain's ``label_comp_id`` sequence against the M5 target's 108 monomers by the
   ungapped offset the RCSB sequence search reports, and writes down which M5 residue indices are
   resolved, which are unresolved, and which carry a different monomer.
3. It records the entry's environment index as the deposition states it: method, resolution or
   model count, crystallisation pH and temperature, every non-polymer component with its count,
   and every other polymer entity present (the binding partners).

Nothing here is a claim about the structure.  Everything it writes is the deposition's own
testimony, relabelled into the M5 target's residue index.

Run:

    python3 research/experiments/m5_predicted_vs_reference/stage_measured.py \
        --measured-root .local/m5-prediction-2026-09-20/measured
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys

# The M5 target, exactly as `extract_sequences.sh` reads it out of the authenticated mmCIF rows.
M5_TARGET = (
    "MAAAMDVDTPSGTNSGAGKKRFEVKKWNAVALWAWDIVVDNCAICRNHIMDLCIECQANQASATSEECTVAWGVCNHAFHFHCISRWLKTRQVCPLDNREWEFQKYGH"
)

THREE_TO_ONE = {
    "ALA": "A", "ARG": "R", "ASN": "N", "ASP": "D", "CYS": "C", "GLN": "Q", "GLU": "E",
    "GLY": "G", "HIS": "H", "ILE": "I", "LEU": "L", "LYS": "K", "MET": "M", "PHE": "F",
    "PRO": "P", "SER": "S", "THR": "T", "TRP": "W", "TYR": "Y", "VAL": "V", "MSE": "M",
    "SEC": "U", "PYL": "O",
}

# What was chosen, and why.  `offset` maps the deposition's own `label_seq_id` to the M5 target's
# 1-based residue index: `m5_index = label_seq_id + offset`.  It comes from the RCSB sequence
# search's ungapped alignment (`query_beg - subject_beg`), and this script CHECKS it monomer by
# monomer rather than trusting it.
CHOSEN = {
    "2LGV": {
        "chain": "A",
        "offset": 8,
        "why": (
            "the only solution-NMR presentation of RBX1 in the RCSB sequence search: 20 deposited "
            "models, so the measured presentation is itself a plural fibre, and RBX1 stands alone "
            "with no cullin partner"
        ),
    },
    "3DPL": {
        "chain": "B",
        "offset": 2,
        "why": (
            "the highest-resolution measured RBX1 in the search (2.6 angstrom X-ray) and the one "
            "with the fewest partners: RBX1 with cullin-5 only"
        ),
    },
    "7Z8R": {
        "chain": "C",
        "offset": 2,
        "why": (
            "a 2.7 angstrom cryo-EM CAND1-CUL1-RBX1 presentation: the measured environment nearest "
            "the M5 release's own CUL1-bound predicted condition, by a third method"
        ),
    },
}


# ------------------------------------------------------------------------------------------------
# a minimal, total mmCIF reader: the loop tokenizer and the single-value items this script needs
# ------------------------------------------------------------------------------------------------

def tokenize(line: str) -> list[str]:
    """mmCIF whitespace tokens, honouring single and double quoting."""
    out: list[str] = []
    at = 0
    while at < len(line):
        if line[at].isspace():
            at += 1
            continue
        if line[at] in "'\"":
            quote = line[at]
            at += 1
            start = at
            while at < len(line) and not (
                line[at] == quote and (at + 1 == len(line) or line[at + 1].isspace())
            ):
                at += 1
            out.append(line[start:at])
            at += 1
            continue
        start = at
        while at < len(line) and not line[at].isspace():
            at += 1
        out.append(line[start:at])
    return out


def atom_site_loop(text: str) -> tuple[list[str], list[list[str]], int, int]:
    """The `_atom_site` loop's headers, its rows, and the line span the loop occupies."""
    lines = text.splitlines()
    at = 0
    while at < len(lines):
        if lines[at].strip() == "loop_":
            probe = at + 1
            headers: list[str] = []
            while probe < len(lines) and lines[probe].strip().startswith("_"):
                headers.append(lines[probe].strip())
                probe += 1
            if headers and headers[0].startswith("_atom_site."):
                rows: list[list[str]] = []
                first_row = probe
                while probe < len(lines):
                    stripped = lines[probe].strip()
                    if stripped.startswith("#") or stripped.startswith("loop_") or (
                        stripped.startswith("_") and not stripped.startswith("_atom_site.")
                    ):
                        break
                    if stripped:
                        rows.append(tokenize(lines[probe]))
                    probe += 1
                return headers, rows, first_row, probe
        at += 1
    raise SystemExit("no _atom_site loop")


# ------------------------------------------------------------------------------------------------
# the staging itself
# ------------------------------------------------------------------------------------------------

def stage(entry: str, root: pathlib.Path, meta: dict) -> dict:
    chosen = CHOSEN[entry]
    source = root / f"{entry}.cif"
    text = source.read_text()
    headers, rows, _, _ = atom_site_loop(text)
    index = {name: at for at, name in enumerate(headers)}

    def cell(row: list[str], name: str, fallback: str = ".") -> str:
        at = index.get(name)
        return row[at] if at is not None and at < len(row) else fallback

    model_column = "_atom_site.pdbx_PDB_model_num"
    models = sorted({cell(r, model_column, "1") for r in rows}, key=lambda m: int(m))

    # The non-polymer complement of the WHOLE deposited file, by component, with the asym chains it
    # sits on.  This is the deposition's ligand testimony and it is recorded, not used.
    ligands: dict[str, list[str]] = {}
    for row in rows:
        if cell(row, "_atom_site.group_PDB") != "HETATM":
            continue
        comp = cell(row, "_atom_site.label_comp_id")
        asym = cell(row, "_atom_site.label_asym_id")
        ligands.setdefault(comp, [])
        if asym not in ligands[comp]:
            ligands[comp].append(asym)

    staged_models = []
    resolved_sets = []
    for model in models:
        keep = [
            row
            for row in rows
            if cell(row, model_column, "1") == model
            and cell(row, "_atom_site.label_asym_id") == chosen["chain"]
            and cell(row, "_atom_site.group_PDB") == "ATOM"
            and cell(row, "_atom_site.label_seq_id") not in (".", "?")
        ]
        if not keep:
            continue
        # A deposited alternate location would give one residue two `CA` atoms, which the
        # library's `labelled_atom` refuses by name.  The altloc complement is recorded and the
        # first-listed alternate is kept, which is a declared choice and is written down.
        alternates = sorted({cell(row, "_atom_site.label_alt_id") for row in keep} - {".", "?"})
        seen_atoms: set[tuple[str, str]] = set()
        deduped = []
        for row in keep:
            key = (cell(row, "_atom_site.label_seq_id"), cell(row, "_atom_site.label_atom_id"))
            if key in seen_atoms:
                continue
            seen_atoms.add(key)
            deduped.append(row)

        residues: dict[int, str] = {}
        for row in deduped:
            residues[int(cell(row, "_atom_site.label_seq_id"))] = cell(
                row, "_atom_site.label_comp_id"
            )
        # only residues that actually carry an alpha carbon are addressable at this receiver
        with_ca = {
            int(cell(row, "_atom_site.label_seq_id"))
            for row in deduped
            if cell(row, "_atom_site.label_atom_id") == "CA"
        }

        m5: dict[int, str] = {}
        typed_mismatch = []
        outside = []
        for ordinal in sorted(with_ca):
            at = ordinal + chosen["offset"]
            if at < 1 or at > len(M5_TARGET):
                outside.append(ordinal)
                continue
            one = THREE_TO_ONE.get(residues[ordinal], "X")
            m5[at] = residues[ordinal]
            if one != M5_TARGET[at - 1]:
                typed_mismatch.append(
                    {"m5_residue": at, "measured": residues[ordinal], "m5": M5_TARGET[at - 1]}
                )
        resolved_sets.append(set(m5))

        out = root / f"{entry}-{chosen['chain']}-model{model}.cif"
        with out.open("w") as handle:
            handle.write(f"data_{entry}_{chosen['chain']}_model{model}\n#\nloop_\n")
            for name in headers:
                handle.write(name + "\n")
            for row in deduped:
                handle.write(" ".join(row) + "\n")
            handle.write("#\n")
        staged_models.append(
            {
                "model": int(model),
                "file": str(out),
                "bytes": out.stat().st_size,
                "atom_rows_kept": len(deduped),
                "atom_rows_dropped_as_alternate_location": len(keep) - len(deduped),
                "alternate_location_labels": alternates,
                "residues_with_an_alpha_carbon": len(with_ca),
                "m5_residues_resolved": sorted(m5),
                "m5_residues_unresolved": [
                    at for at in range(1, len(M5_TARGET) + 1) if at not in m5
                ],
                "monomer_differs_from_the_m5_target_at": typed_mismatch,
                "label_seq_ids_outside_the_m5_index": outside,
            }
        )

    common = set.intersection(*resolved_sets) if resolved_sets else set()
    entry_meta = meta.get(entry, {})
    return {
        "entry": entry,
        "chain_label_asym_id": chosen["chain"],
        "why_chosen": chosen["why"],
        "label_seq_id_to_m5_offset": chosen["offset"],
        "source_file": str(source),
        "source_bytes": source.stat().st_size,
        "deposited_models": len(models),
        "environment_index_as_deposited": entry_meta,
        "non_polymer_components_in_the_whole_file": {
            comp: len(asyms) for comp, asyms in sorted(ligands.items())
        },
        "zinc_copies_in_the_whole_file": len(ligands.get("ZN", [])),
        "models_staged": staged_models,
        "m5_residues_resolved_in_every_model": sorted(common),
        "m5_residues_unresolved_in_some_model": sorted(
            set(range(1, len(M5_TARGET) + 1)) - common
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--measured-root", default=".local/m5-prediction-2026-09-20/measured")
    parser.add_argument("--out", default=None)
    args = parser.parse_args()
    root = pathlib.Path(args.measured_root)

    meta: dict[str, dict] = {}
    entries_file = root / "entries.json"
    if entries_file.exists():
        raw = json.loads(entries_file.read_text())
        for entry in raw.get("data", {}).get("entries", []) or []:
            if not entry:
                continue
            info = entry.get("rcsb_entry_info") or {}
            grow = (entry.get("exptl_crystal_grow") or [{}])[0] or {}
            partners = [
                {
                    "entity": p["rcsb_id"],
                    "description": (p.get("rcsb_polymer_entity") or {}).get("pdbx_description"),
                    "asym_ids": (p.get("rcsb_polymer_entity_container_identifiers") or {}).get(
                        "asym_ids"
                    ),
                    "length": (p.get("entity_poly") or {}).get("rcsb_sample_sequence_length"),
                }
                for p in (entry.get("polymer_entities") or [])
            ]
            meta[entry["rcsb_id"]] = {
                "method": [m["method"] for m in (entry.get("exptl") or [])],
                "resolution_angstrom": (info.get("resolution_combined") or [None])[0],
                "deposited_model_count": info.get("deposited_model_count"),
                "title": (entry.get("struct") or {}).get("title"),
                "crystallisation_pH": grow.get("pH"),
                "crystallisation_temperature_kelvin": grow.get("temp"),
                "crystallisation_details": grow.get("pdbx_details"),
                "polymer_entities_present": partners,
            }

    staged = [stage(entry, root, meta) for entry in sorted(CHOSEN)]
    common = set.intersection(
        *[set(one["m5_residues_resolved_in_every_model"]) for one in staged]
    )
    typed_disagreement = sorted(
        {
            row["m5_residue"]
            for one in staged
            for model in one["models_staged"]
            for row in model["monomer_differs_from_the_m5_target_at"]
        }
    )
    result = {
        "schema": "holonics.m5-measured-staging.v1",
        "m5_target_108": M5_TARGET,
        "what_the_filter_did": (
            "kept the ATOM rows of one label_asym_id in one pdbx_PDB_model_num that carry an "
            "integer label_seq_id and are not a repeated alternate location; copied every "
            "coordinate token verbatim; wrote the source's own _atom_site header"
        ),
        "entries": staged,
        "m5_residues_resolved_in_every_measured_model": sorted(common),
        "m5_residues_whose_monomer_differs_in_some_measured_entry": typed_disagreement,
        "m5_residues_resolved_and_identically_typed_in_every_measured_model": sorted(
            common - set(typed_disagreement)
        ),
    }
    text = json.dumps(result, indent=2)
    if args.out:
        pathlib.Path(args.out).write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
