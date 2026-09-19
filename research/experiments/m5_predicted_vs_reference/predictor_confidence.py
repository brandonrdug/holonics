#!/usr/bin/env python3
"""Read Boltz-2's own confidence outputs for the M5 runs.

[definition] EXTERIOR FLOAT STATISTICS. pLDDT and PAE are the predictor's self-report. They are
read here, printed here, and enter no library call: the repository's receivers decide over exact
rationals and never over a predictor's confidence. Run with the protein virtual environment's
python, which carries numpy:

    .local/venv-protein/bin/python research/experiments/m5_predicted_vs_reference/predictor_confidence.py \
        .local/m5-prediction-2026-09-19
"""
import json
import pathlib
import sys

import numpy as np

RUNS = [
    ("boltz2-target-seed0", "out-target-only/boltz_results_target-only/predictions/target-only", "target-only"),
    ("boltz2-target-seed1", "out-target-only-seed1/boltz_results_target-only-seed1/predictions/target-only-seed1", "target-only-seed1"),
    ("boltz2-complex-seed0", "out-binder-target/boltz_results_binder-target/predictions/binder-target", "binder-target"),
    ("boltz2-complex-seed1", "out-binder-target-seed1/boltz_results_binder-target-seed1/predictions/binder-target-seed1", "binder-target-seed1"),
]
# The target chain is first in every input, so its tokens are the leading 108 rows.
TARGET = 108


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".local/m5-prediction-2026-09-19")
    rows = []
    for name, where, stem in RUNS:
        directory = root / where
        confidence = json.loads((directory / f"confidence_{stem}_model_0.json").read_text())
        plddt = np.load(directory / f"plddt_{stem}_model_0.npz")["plddt"].squeeze()
        pae = np.load(directory / f"pae_{stem}_model_0.npz")["pae"].squeeze()
        rows.append({
            "presentation": name,
            "confidence_score": confidence["confidence_score"],
            "ptm": confidence["ptm"],
            "iptm": confidence["iptm"] or None,
            "complex_plddt": confidence["complex_plddt"],
            "chains_ptm": confidence["chains_ptm"],
            "mean_plddt_target_108": float(plddt[:TARGET].mean()),
            "mean_plddt_target_core_21_108": float(plddt[20:TARGET].mean()),
            "mean_plddt_target_arm_1_20": float(plddt[:20].mean()),
            "mean_plddt_binder_96": float(plddt[TARGET:].mean()) if plddt.shape[0] > TARGET else None,
            "mean_pae_target_core_21_108": float(pae[20:TARGET, 20:TARGET].mean()),
            "mean_pae_target_arm_1_20": float(pae[:20, :20].mean()),
            "mean_pae_interface": (
                float(pae[:TARGET, TARGET:].mean()) if pae.shape[0] > TARGET else None
            ),
            "tokens": int(plddt.shape[0]),
        })
    print(json.dumps({
        "schema": "holonics.m5-predictor-confidence.v1",
        "note": "exterior float statistics; the predictor's own self-report, never a library input",
        "rows": rows,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
