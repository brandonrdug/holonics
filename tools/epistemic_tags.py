#!/usr/bin/env python3
"""Verify paragraph-leading epistemic brackets on live HIF authority and formal prerequisites.

The vocabulary is read from `canon/EPISTEMIC_GRADES.md`; this tool owns no parallel list. A
material bracket must contain exactly one truth-status grade and may contain only evidence tags
declared by the same canon file.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRADES = ROOT / "canon" / "EPISTEMIC_GRADES.md"
LIVE = [
    ROOT / "CONSTRUCTION_STATE.md",
    ROOT / "blueprint" / "THE_ROADMAP.md",
    ROOT
    / "blueprint"
    / "THE_HOLONIC_INTELLIGENCE_FRAMEWORK_RETURNS_INTRINSIC_HOLONS_AND_PACKAGES_DISMANTLING_INFERENCE_CULTIVATION_AND_GENERATION.md",
    ROOT
    / "blueprint"
    / "THE_HOLONIC_NEURAL_ECOLOGY_RETURNS_EVERY_CLASSICAL_ARCHITECTURE_AS_A_RECEIVER_CHART_AND_EROS_CULTIVATES_ATHENA_THROUGH_PHYSICAL_INFORMATION_TRANSPORT.md",
    ROOT
    / "blueprint"
    / "THE_CLASSICAL_MACHINE_LEARNING_CHART_DESCENDS_FROM_HOLONIC_TRANSPORT_AND_HIGHER_CAUSAL_FIBRES_REOPEN_ITS_COLLAPSED_STATES.md",
    ROOT
    / "research"
    / "records"
    / "2026-08-31_HOLONIC_INTELLIGENCE_REQUIRES_INTRINSIC_PROFILES_AND_NEUTRAL_LIFECYCLE_INTERFACES.md",
]

LEADING = re.compile(r"^\[([a-z0-9-]+(?:;\s*[a-z0-9-]+)*)\](?:\s|$)")
ROW = re.compile(r"^\|\s*`([^`]+)`\s*\|")


def vocabulary() -> tuple[set[str], set[str]]:
    truth: set[str] = set()
    evidence: set[str] = set()
    section: str | None = None
    for line in GRADES.read_text().splitlines():
        if line == "## Truth-status grades":
            section = "truth"
            continue
        if line == "## Evidence tags":
            section = "evidence"
            continue
        if line.startswith("## ") and line not in {"## Truth-status grades", "## Evidence tags"}:
            section = None
        match = ROW.match(line)
        if not match or section is None:
            continue
        (truth if section == "truth" else evidence).add(match.group(1))
    if not truth or not evidence:
        raise RuntimeError("epistemic vocabulary could not be read from canon/EPISTEMIC_GRADES.md")
    return truth, evidence


def main() -> int:
    truth, evidence = vocabulary()
    failures: list[str] = []
    checked = 0
    for path in LIVE:
        if not path.is_file():
            failures.append(f"MISSING {path.relative_to(ROOT)}")
            continue
        for number, line in enumerate(path.read_text(errors="replace").splitlines(), start=1):
            match = LEADING.match(line)
            if not match:
                continue
            checked += 1
            tags = [part.strip() for part in match.group(1).split(";")]
            truths = [tag for tag in tags if tag in truth]
            unknown = [tag for tag in tags if tag not in truth and tag not in evidence]
            if len(truths) != 1 or unknown:
                failures.append(
                    f"{path.relative_to(ROOT)}:{number}: truths={truths} unknown={unknown} tags={tags}"
                )
    for failure in failures:
        print(f"EPISTEMIC {failure}")
    print(
        f"epistemic-tags: {checked} material brackets checked across {len(LIVE)} live authorities; "
        f"{len(failures)} failures"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
