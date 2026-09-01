#!/usr/bin/env python3
"""Require the live HIF authority and its named formal owners to exist in the Git index."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REQUIRED = [
    "AGENTS.md",
    "CLAUDE.md",
    "CONSTRUCTION_STATE.md",
    "blueprint/THE_ROADMAP.md",
    "blueprint/THE_HOLONIC_INTELLIGENCE_FRAMEWORK_RETURNS_INTRINSIC_HOLONS_AND_PACKAGES_DISMANTLING_INFERENCE_CULTIVATION_AND_GENERATION.md",
    "blueprint/THE_HOLONIC_NEURAL_ECOLOGY_RETURNS_EVERY_CLASSICAL_ARCHITECTURE_AS_A_RECEIVER_CHART_AND_EROS_CULTIVATES_ATHENA_THROUGH_PHYSICAL_INFORMATION_TRANSPORT.md",
    "blueprint/THE_CLASSICAL_MACHINE_LEARNING_CHART_DESCENDS_FROM_HOLONIC_TRANSPORT_AND_HIGHER_CAUSAL_FIBRES_REOPEN_ITS_COLLAPSED_STATES.md",
    "research/records/2026-08-31_HOLONIC_INTELLIGENCE_REQUIRES_INTRINSIC_PROFILES_AND_NEUTRAL_LIFECYCLE_INTERFACES.md",
    "research/records/2026-08-31_HIF0_INTRINSIC_HOLON_PROFILES_AND_NEUTRAL_LIFECYCLE_CONTRACTS_RETURNED.md",
    "research/records/2026-08-31_HIF1_GENERIC_RUST_PROFILE_AND_RESTED_TRANSPORT_SURFACE_RETURNED.md",
    "research/records/2026-08-31_HIF2_EXACT_FOREIGN_CHARTS_LOW_PRECISION_WEIGHTS_AND_PROFILED_DISMANTLING_RETURNED.md",
    "crates/holonic-engine/src/addressed_current.rs",
    "crates/holonic-engine/src/factored_moment.rs",
    "soma/life/src/athena_native/source_neutral_relational.rs",
    "soma/life/src/athena_native/source_neutral_rest.rs",
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicMachineLearning.lean",
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/IntrinsicHolonProfile.lean",
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicIntelligenceLifecycle.lean",
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/ExactForeignWeight.lean",
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicIntelligenceFramework.lean",
    "crates/holonic-engine/src/holonic_intelligence.rs",
    "crates/holonic-engine/src/holonic_intelligence/dimensions.rs",
    "crates/holonic-engine/src/holonic_intelligence/lifecycle.rs",
    "crates/holonic-engine/src/holonic_intelligence/profile.rs",
    "crates/holonic-engine/src/holonic_intelligence/rested.rs",
    "crates/holonic-engine/src/holonic_intelligence/foreign_json.rs",
    "crates/holonic-engine/src/holonic_intelligence/foreign_onnx.rs",
    "crates/holonic-engine/src/holonic_intelligence/weight.rs",
    "crates/holonic-engine/src/foreign_map/coverage.rs",
    "crates/holonic-engine/examples/inspect_foreign_model_charts_hif2.rs",
    "soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean",
]


def tracked(path: str) -> bool:
    result = subprocess.run(
        ["git", "ls-files", "--error-unmatch", "--", path],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def main() -> int:
    missing = [path for path in REQUIRED if not (ROOT / path).is_file()]
    untracked = [path for path in REQUIRED if (ROOT / path).is_file() and not tracked(path)]
    for path in missing:
        print(f"MISSING   {path}")
    for path in untracked:
        print(f"UNTRACKED {path}")
    print(
        f"tracked-authority: {len(REQUIRED) - len(missing) - len(untracked)}/{len(REQUIRED)} "
        f"required live paths tracked; {len(missing)} missing, {len(untracked)} untracked"
    )
    return 1 if missing or untracked else 0


if __name__ == "__main__":
    sys.exit(main())
