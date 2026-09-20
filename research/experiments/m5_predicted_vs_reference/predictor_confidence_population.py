#!/usr/bin/env python3
"""Boltz-2's own confidence over the 2026-09-20 seed population.

[definition] EXTERIOR FLOAT STATISTICS. pLDDT, PAE and the confidence score are the predictor's
self-report. They are read here, printed here, and enter no library call: the repository's
receivers decide over exact rationals and never over a predictor's confidence. This is the
2026-09-19 `predictor_confidence.py` widened from four named runs to the whole population's
directory layout; it adds nothing else.

    .local/venv-protein/bin/python \
        research/experiments/m5_predicted_vs_reference/predictor_confidence_population.py \
        .local/m5-prediction-2026-09-20/out
"""
import json
import pathlib
import sys

import numpy as np

TARGET = 108
CONDITIONS = ["target", "target-zn", "complex", "complex-zn"]


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".local/m5-prediction-2026-09-20/out")
    rows = []
    for condition in CONDITIONS:
        for seed in range(64):
            where = root / f"{condition}-seed{seed}" / f"boltz_results_{condition}" / "predictions" / condition
            confidence_file = where / f"confidence_{condition}_model_0.json"
            if not confidence_file.exists():
                continue
            confidence = json.loads(confidence_file.read_text())
            plddt = np.load(where / f"plddt_{condition}_model_0.npz")["plddt"].squeeze()
            pae = np.load(where / f"pae_{condition}_model_0.npz")["pae"].squeeze()
            carries_binder = condition.startswith("complex")
            rows.append({
                "presentation": f"boltz2-{condition}-seed{seed}",
                "group": f"boltz2-{condition}",
                "seed": seed,
                "zinc_supplied": condition.endswith("-zn"),
                "carries_binder": carries_binder,
                "tokens": int(plddt.shape[0]),
                "confidence_score": confidence["confidence_score"],
                "ptm": confidence["ptm"],
                "iptm": confidence["iptm"] or None,
                "complex_plddt": confidence["complex_plddt"],
                "mean_plddt_target_108": float(plddt[:TARGET].mean()),
                "mean_plddt_target_core_21_108": float(plddt[20:TARGET].mean()),
                "mean_plddt_target_arm_1_20": float(plddt[:20].mean()),
                "mean_plddt_commonly_resolved_21_106": float(plddt[20:106].mean()),
                "mean_plddt_binder_96": (
                    float(plddt[TARGET:TARGET + 96].mean()) if carries_binder else None
                ),
                "mean_plddt_zinc_tokens": (
                    float(plddt[-3:].mean()) if condition.endswith("-zn") else None
                ),
                "mean_pae_target_core_21_108": float(pae[20:TARGET, 20:TARGET].mean()),
                "mean_pae_target_arm_1_20": float(pae[:20, :20].mean()),
                "mean_pae_interface": (
                    float(pae[:TARGET, TARGET:TARGET + 96].mean()) if carries_binder else None
                ),
            })
    summary = {}
    for condition in CONDITIONS:
        members = [row for row in rows if row["group"] == f"boltz2-{condition}"]
        if not members:
            continue
        def over(key):
            values = sorted(row[key] for row in members if row[key] is not None)
            if not values:
                return None
            return {
                "population": len(values),
                "minimum": values[0],
                "median": values[len(values) // 2],
                "maximum": values[-1],
            }
        summary[f"boltz2-{condition}"] = {
            "confidence_score": over("confidence_score"),
            "mean_plddt_target_arm_1_20": over("mean_plddt_target_arm_1_20"),
            "mean_plddt_target_core_21_108": over("mean_plddt_target_core_21_108"),
            "iptm": over("iptm"),
            "mean_plddt_zinc_tokens": over("mean_plddt_zinc_tokens"),
        }
    print(json.dumps({
        "schema": "holonics.m5-predictor-confidence-population.v1",
        "note": "exterior float statistics; the predictor's own self-report, never a library input",
        "rows": rows,
        "per_group_spread": summary,
    }, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
