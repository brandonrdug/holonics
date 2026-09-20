#!/usr/bin/env python3
"""Assemble the 2026-09-20 presentation manifest: measured, designed, and the seed population.

[definition] This script **computes no receiver reading**. It lists every presentation the Rust
example is to mount, with the environment index each one's own source states, and it stages two
kinds of file the library's mmCIF intake cannot read as deposited:

* a Boltz-2 prediction **with zinc** writes its `ZN` ions as `HETATM` rows whose
  `_atom_site.label_seq_id` is `.`, and `physical_intake::mmcif` requires an integer there.  The
  protein rows are written to a `-protein.cif` beside the prediction, token for token.
* the measured entries are staged by `stage_measured.py`, which this script reads rather than
  repeats.

Beside each zinc prediction it records, as **exterior float and load-bearing for nothing**, the
four protein atoms nearest each placed `ZN` — the one cheap way to see whether the predictor put
the ions in RBX1's RING cross-brace or somewhere else.  Nothing downstream reads it.

Run:

    python3 research/experiments/m5_predicted_vs_reference/assemble_manifest.py \
        --population-root .local/m5-prediction-2026-09-20/out \
        --staging .local/m5-prediction-2026-09-20/measured/staging.json \
        --structure-root <M5_STRUCTURE_ROOT> \
        --out .local/m5-prediction-2026-09-20/manifest.json
"""

from __future__ import annotations

import os
import argparse
import json
import math
import pathlib

M5_TARGET = (
    "MAAAMDVDTPSGTNSGAGKKRFEVKKWNAVALWAWDIVVDNCAICRNHIMDLCIECQANQASATSEECTVAWGVCNHAFHFHCISRWLKTRQVCPLDNREWEFQKYGH"
)
BINDER = (
    "MSPLEEVIEKGEELIRELGEKYNIPKEVTEKLIELFREYLEKYGVSNEAFRNFLKESLEILLKSGVPKEKAFDFVIELGAELTRWLFWKLRQKGLE"
)

# The declared minimum chain separation of the within-component contact receiver.  Two occurrences
# one or two positions apart on the chain are inside any protein aperture whatever the fold does,
# so they carry no reading; `found_within_component_contact_family` refuses a separation below 2
# as covalent, and 3 is declared here so that i,i+2 is excluded as well.
MINIMUM_SEPARATION = 3

CONDITIONS = {
    "target": {
        "carries_binder": False,
        "zinc": 0,
        "conformation": "predicted_target_alone",
        "conformation_ground": "the target sequence was folded with no partner and no ion at all",
    },
    "target-zn": {
        "carries_binder": False,
        "zinc": 3,
        "conformation": "predicted_target_alone_with_zinc",
        "conformation_ground": (
            "the target sequence was folded with three ZN ion entities and no protein partner; no "
            "pocket or contact constraint was supplied, so where the ions went is the predictor's "
            "own statement and not a placement this experiment made"
        ),
    },
    "complex": {
        "carries_binder": True,
        "zinc": 0,
        "conformation": "predicted_free",
        "conformation_ground": "the binder and the target were cofolded with no third partner",
    },
    "complex-zn": {
        "carries_binder": True,
        "zinc": 3,
        "conformation": "predicted_free_with_zinc",
        "conformation_ground": (
            "the binder and the target were cofolded with three ZN ion entities and no third "
            "protein partner; no pocket or contact constraint was supplied"
        ),
    },
}

MSA_GROUND = {
    False: (
        "Boltz-2 2.2.1 single-chain folding; MSA read from the 2026-09-19 run's own emitted csv by "
        "path (11,248 rows), so no server call was made and the MSA is byte-identical across every "
        "seed of this population"
    ),
    True: (
        "Boltz-2 2.2.1 cofolding; both chains' MSAs read from the 2026-09-19 run's own emitted csv "
        "files by path (target 11,248 rows, de novo binder 1 row), so no server call was made and "
        "the MSA is byte-identical across every seed of this population"
    ),
}


# ------------------------------------------------------------------------------------------------

def tokenize(line: str) -> list[str]:
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


def atom_site_loop(text: str) -> tuple[list[str], list[list[str]]]:
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
                rows = []
                while probe < len(lines):
                    stripped = lines[probe].strip()
                    if stripped.startswith("#") or stripped.startswith("loop_") or (
                        stripped.startswith("_") and not stripped.startswith("_atom_site.")
                    ):
                        break
                    if stripped:
                        rows.append(tokenize(lines[probe]))
                    probe += 1
                return headers, rows
        at += 1
    raise SystemExit("no _atom_site loop")


def stage_protein_only(source: pathlib.Path) -> tuple[pathlib.Path, dict]:
    """Write the ATOM rows with an integer `label_seq_id`, and report the ion coordination."""
    headers, rows = atom_site_loop(source.read_text())
    index = {name: at for at, name in enumerate(headers)}

    def cell(row, name, fallback="."):
        at = index.get(name)
        return row[at] if at is not None and at < len(row) else fallback

    protein, ions = [], []
    for row in rows:
        seq = cell(row, "_atom_site.label_seq_id")
        if cell(row, "_atom_site.group_PDB") == "ATOM" and seq not in (".", "?"):
            protein.append(row)
        elif cell(row, "_atom_site.label_comp_id") == "ZN":
            ions.append(row)

    out = source.with_name(source.stem + "-protein.cif")
    with out.open("w") as handle:
        handle.write(f"data_{source.stem}_protein\n#\nloop_\n")
        for name in headers:
            handle.write(name + "\n")
        for row in protein:
            handle.write(" ".join(row) + "\n")
        handle.write("#\n")

    # exterior float, load-bearing for nothing: what each ion's four nearest protein atoms are
    def place(row):
        return (
            float(cell(row, "_atom_site.Cartn_x")),
            float(cell(row, "_atom_site.Cartn_y")),
            float(cell(row, "_atom_site.Cartn_z")),
        )

    coordination = []
    protein_places = [
        (
            cell(row, "_atom_site.label_asym_id"),
            int(cell(row, "_atom_site.label_seq_id")),
            cell(row, "_atom_site.label_comp_id"),
            cell(row, "_atom_site.label_atom_id"),
            place(row),
        )
        for row in protein
    ]
    for at, ion in enumerate(ions):
        ip = place(ion)
        near = sorted(
            (
                (math.dist(ip, p[4]), p[0], p[1], p[2], p[3])
                for p in protein_places
            ),
            key=lambda entry: entry[0],
        )[:4]
        coordination.append(
            {
                "ion": at + 1,
                "exterior_float_nearest_protein_atoms": [
                    {
                        "chain": n[1],
                        "label_seq_id": n[2],
                        "monomer": n[3],
                        "atom": n[4],
                        "exterior_float_distance_angstrom": round(n[0], 3),
                    }
                    for n in near
                ],
            }
        )
    return out, {
        "zinc_ions_in_the_prediction": len(ions),
        "protein_atom_rows_kept": len(protein),
        "exterior_float_ion_coordination": coordination,
    }


# ------------------------------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--population-root", default=".local/m5-prediction-2026-09-20/out")
    parser.add_argument("--staging", default=".local/m5-prediction-2026-09-20/measured/staging.json")
    parser.add_argument("--structure-root", default=os.environ.get("HOLONICS_M5_STRUCTURE_ROOT", ""))
    parser.add_argument("--out", default=".local/m5-prediction-2026-09-20/manifest.json")
    args = parser.parse_args()

    staging = json.loads(pathlib.Path(args.staging).read_text())
    structure_root = pathlib.Path(args.structure_root)
    presentations: list[dict] = []
    ion_reports: dict[str, dict] = {}

    def add(**row):
        row.setdefault("target_chain_label_asym_id", None)
        row.setdefault("binder_chain_label_asym_id", None)
        row.setdefault("label_seq_id_to_m5_offset", 0)
        row.setdefault("acidity", None)
        row.setdefault("solvation", None)
        presentations.append(row)

    # ------------------------------------------------------------------------------- the measured
    for entry in staging["entries"]:
        env = entry["environment_index_as_deposited"]
        method = (env.get("method") or ["undeclared"])[0]
        partners = env.get("polymer_entities_present") or []
        copies = {}
        for partner in partners:
            description = (partner.get("description") or "").lower()
            if "rbx1" in description or "ring-box" in description:
                copies["RBX1"] = 1
            elif "cullin-5" in description:
                copies["CUL5"] = 1
            elif "cullin-1" in description or description.startswith("cullin homolog 1"):
                copies["CUL1"] = 1
            elif "cullin-associated" in description:
                copies["CAND1"] = 1
            else:
                copies[(partner.get("description") or "unnamed")[:24]] = 1
        resolution = env.get("resolution_angstrom")
        detail = (
            f"{resolution} angstrom" if resolution else f"{entry['deposited_models']} deposited models"
        )
        acidity = None
        if env.get("crystallisation_pH") is not None:
            acidity = {
                "p_h": str(env["crystallisation_pH"]),
                "protonation_assumption": (
                    "none is deposited; the value is the crystallisation liquor's pH as the entry "
                    "states it in exptl_crystal_grow, which is the pH the crystal grew at and not "
                    "a protonation model of the refined coordinates"
                ),
                "ground": f"RCSB entry {entry['entry']} exptl_crystal_grow.pH",
            }
        for model in entry["models_staged"]:
            suffix = f"-m{model['model']}" if entry["deposited_models"] > 1 else ""
            add(
                name=f"measured-{entry['entry']}{suffix}",
                group=f"measured-{entry['entry']}",
                file=model["file"],
                target_chain_label_asym_id=entry["chain_label_asym_id"],
                label_seq_id_to_m5_offset=entry["label_seq_id_to_m5_offset"],
                occurrence_kind={"measured": {"apparatus": f"{method}, {detail}"}},
                conformation=f"measured_{entry['entry'].lower()}_model{model['model']}",
                conformation_ground=(
                    f"RCSB entry {entry['entry']}, chain label_asym_id "
                    f"{entry['chain_label_asym_id']}, deposited model {model['model']}: "
                    + (env.get("title") or "")
                ),
                assay={"declared": {"description": f"{method}, {detail}, RCSB {entry['entry']}"}},
                assay_ground="the deposition's own exptl.method and resolution or model count",
                cofactors={"ZN": entry["zinc_copies_in_the_whole_file"]}
                if entry["zinc_copies_in_the_whole_file"]
                else {},
                cofactor_ground=(
                    "the non-polymer entities the deposited entry carries, counted by asym chain; "
                    "the staged coordinate file carries the protein chain only, and the ion "
                    "complement is the entry's testimony about what was present"
                ),
                oligomeric_copies=copies,
                acidity=acidity,
                declaration=(
                    f"declared for a measured presentation: RCSB {entry['entry']} deposits "
                    "coordinates and a method but none of the eleven environment arrays this "
                    "intake reads; the token population is the staged chain's own residues"
                ),
                ecology={
                    "target": "RBX1",
                    "target_form": f"measured_{entry['entry'].lower()}",
                    "stoichiometry": "to".join(["1"] * max(len(copies), 1)),
                    "cofolding_model": "none: this is a measured structure, not a prediction",
                },
                lineage={
                    "design_uuid": "m5-rbx1-rank05",
                    "design_name": f"rcsb-{entry['entry']}",
                    "seed": f"model-{model['model']}",
                },
                measured_entry=entry["entry"],
                ensemble_model=model["model"],
                seed=None,
            )

    # ------------------------------------------------------- the design and the release's Protenix
    add(
        name="designed",
        group="designed",
        file=str(structure_root / "designed-free-rbx1.cif"),
        occurrence_kind={"designed": {"generator": "the M5 release's own design generator"}},
        conformation="designed_free",
        conformation_ground="the M5 release names this file the designed free structure",
        assay={"declared": {"description": "a design generator's emitted structure, not a prediction"}},
        assay_ground="the designed structure is emitted by the design pipeline itself",
        cofactors={"ZN": 3},
        cofactor_ground="the zinc heteroatom occurrences actually present in the mounted mmCIF",
        oligomeric_copies={"RBX1": 1, "binder": 1},
        declaration=(
            "declared for the designed structure, which carries no uncertainty array at all: the "
            "token population is the designed mmCIF's own two protein chains"
        ),
        ecology={
            "target": "RBX1",
            "target_form": "designed_free",
            "stoichiometry": "1to1",
            "cofolding_model": "none: this is a designed structure, not a prediction",
        },
        lineage={"design_uuid": "m5-rbx1-rank05", "design_name": "m5-rbx1-rank05", "seed": "none"},
        carries_binder=True,
        seed=None,
    )
    for name, cif, form, seed in [
        ("protenix-free", "ptxv2-free-rbx1-seed2.cif", "predicted_free", "2"),
        ("protenix-cul1", "ptxv2-cul1-rbx1-seed0.cif", "predicted_cul1_bound", "0"),
    ]:
        copies = {"RBX1": 1, "binder": 1}
        if form == "predicted_cul1_bound":
            copies["CUL1"] = 1
        add(
            name=name,
            group=name,
            file=str(structure_root / cif),
            occurrence_kind={"predicted": {"predictor": "Protenix v2", "seed": seed}},
            conformation=form,
            conformation_ground=f"the M5 release names this run the {form} prediction",
            assay={"in_silico": {"predictor": "Protenix v2 cofolding", "seed": seed}},
            assay_ground="the release names Protenix v2 as the predictor",
            cofactors={"ZN": 3},
            cofactor_ground="the zinc heteroatom occurrences actually present in the mounted mmCIF",
            oligomeric_copies=copies,
            declaration="declared for a Protenix v2 run staged by the M5 release",
            ecology={
                "target": "RBX1",
                "target_form": form,
                "stoichiometry": "1to1to1" if "CUL1" in copies else "1to1",
                "cofolding_model": "protenix-v2",
            },
            lineage={
                "design_uuid": "m5-rbx1-rank05",
                "design_name": "m5-rbx1-rank05",
                "seed": seed,
            },
            carries_binder=True,
            seed=None,
        )

    # -------------------------------------------------------------------------- the seed population
    root = pathlib.Path(args.population_root)
    for condition, declared in CONDITIONS.items():
        for seed in range(64):
            source = (
                root
                / f"{condition}-seed{seed}"
                / f"boltz_results_{condition}"
                / "predictions"
                / condition
                / f"{condition}_model_0.cif"
            )
            if not source.exists():
                continue
            name = f"boltz2-{condition}-seed{seed}"
            file = source
            if declared["zinc"]:
                file, report = stage_protein_only(source)
                ion_reports[name] = report
            copies = {"RBX1": 1}
            if declared["carries_binder"]:
                copies["binder"] = 1
            add(
                name=name,
                group=f"boltz2-{condition}",
                file=str(file),
                occurrence_kind={"predicted": {"predictor": "Boltz-2 2.2.1", "seed": str(seed)}},
                conformation=declared["conformation"],
                conformation_ground=declared["conformation_ground"],
                assay={
                    "in_silico": {
                        "predictor": "Boltz-2 2.2.1 "
                        + ("cofolding" if declared["carries_binder"] else "single-chain folding")
                        + (", with three ZN ion entities" if declared["zinc"] else ""),
                        "seed": str(seed),
                    }
                },
                assay_ground=MSA_GROUND[declared["carries_binder"]],
                cofactors={"ZN": declared["zinc"]} if declared["zinc"] else {},
                cofactor_ground=(
                    "three ZN ion entities were supplied to the predictor and three ZN sites are "
                    "present in its output"
                    if declared["zinc"]
                    else "no ligand was supplied to this predictor and none is present in its "
                    "output; the empty complement is that statement and not a default"
                ),
                oligomeric_copies=copies,
                declaration=(
                    "declared for a Boltz-2 run, which emits confidence arrays but none of the "
                    "eleven environment arrays this intake reads"
                ),
                ecology={
                    "target": "RBX1",
                    "target_form": declared["conformation"],
                    "stoichiometry": "1to1" if declared["carries_binder"] else "1",
                    "cofolding_model": "boltz2-2.2.1",
                },
                lineage={
                    "design_uuid": "m5-rbx1-rank05",
                    "design_name": "m5-rbx1-rank05",
                    "seed": str(seed),
                },
                carries_binder=declared["carries_binder"],
                seed=seed,
                source_prediction=str(source),
            )

    manifest = {
        "schema": "holonics.m5-presentation-manifest.v1",
        "dated": "2026-09-20",
        "target_sequence": M5_TARGET,
        "binder_sequence": BINDER,
        "minimum_chain_separation": MINIMUM_SEPARATION,
        "commonly_resolved_m5_residues": staging["m5_residues_resolved_in_every_measured_model"],
        "commonly_resolved_and_identically_typed_m5_residues": staging[
            "m5_residues_resolved_and_identically_typed_in_every_measured_model"
        ],
        "m5_residues_whose_monomer_differs_in_some_measured_entry": staging[
            "m5_residues_whose_monomer_differs_in_some_measured_entry"
        ],
        "exterior_float_zinc_coordination": ion_reports,
        "presentations": presentations,
    }
    pathlib.Path(args.out).write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        f"{len(presentations)} presentations -> {args.out}\n"
        f"  measured models: {sum(1 for p in presentations if 'measured_entry' in p)}\n"
        f"  boltz population: {sum(1 for p in presentations if p.get('seed') is not None)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
