#!/usr/bin/env python3
"""Bind every returned artifact under `output/` to its content hash, in a TRACKED file.

`.gitignore` says it in its own first lines: *"A driver writes its returns under `/output/`. That
directory is ignored, and an ignored `/output/` is a return the repository cannot certify and can
lose."* The repository knew, said so, and lost evidence to that sink anyway — the residue-stratum
atlas is under `output/` on disk right now with no commit behind it, and the tiger phase atlas went
the same way through `target/`.

This does not track the artifacts. It tracks the one thing that makes a loss *detectable and
reportable*: the address. Brandon authorized removal of the accumulated ignored output population
on 2026-08-30; its last pre-clean content inventory is preserved under
`meta/history/2026-08-30_OUTPUT_MANIFEST_PRE_CLEANUP.tsv`. The live manifest is intentionally empty
until a later driver returns new material.

    python3 tools/output_manifest.py           # rewrite meta/OUTPUT_MANIFEST.tsv
    python3 tools/output_manifest.py --check    # exit 1 if the tree disagrees with the manifest
    python3 tools/output_manifest.py --files    # print the per-artifact listing, write nothing

**One line per driver, not per artifact.** The first form of this tool recorded every file, and a
single `eros_morphological_language_generation` run deposited 13,154 `.form` artifacts and took the
tracked manifest to 14,046 lines and 2.7 MB. A manifest that grows by thirteen thousand lines per run
becomes the clutter it exists to prevent.

The roll-up loses nothing that matters, because **the loss this file exists to catch is a directory
vanishing**, not one artifact inside one. `returns` and `bytes` move if any artifact is added or
removed; `sha256` is taken over the sorted per-artifact addresses, so it moves if any byte of any
artifact changes. `--files` reconstructs the full listing on demand. There is no threshold and no
aperture: every driver directory is rolled up, uniformly.

`CLAUDE.md`'s retained deposit law is: bind every deposit to its content hash and its closure hash,
with a verifier. This is the content half; `tools/closure_manifest.py` owns the transitive Cargo,
build-script, CUDA, toolchain, and path-dependency closure half.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "output"
MANIFEST = ROOT / "meta" / "OUTPUT_MANIFEST.tsv"
HEADER = "sha256\treturns\tbytes\tdriver"


def digest(path: Path) -> tuple[str, int]:
    """Content address and extent. Streamed — driver returns reach hundreds of megabytes."""
    accumulator = hashlib.sha256()
    extent = 0
    with path.open("rb") as handle:
        while chunk := handle.read(1 << 20):
            accumulator.update(chunk)
            extent += len(chunk)
    return accumulator.hexdigest(), extent


def artifacts(directory: Path) -> list[tuple[str, int, str]]:
    """Every regular artifact under one driver, in canonical order."""
    found: list[tuple[str, int, str]] = []
    for path in sorted(directory.rglob("*")):
        if not path.is_file() or path.is_symlink():
            continue
        address, extent = digest(path)
        found.append((address, extent, str(path.relative_to(ROOT))))
    return found


def survey() -> list[tuple[str, int, int, str]]:
    """One row per driver: the rolled-up address, the return count, the extent, the driver."""
    if not OUTPUT.is_dir():
        return []
    rows: list[tuple[str, int, int, str]] = []
    for directory in sorted(OUTPUT.iterdir()):
        if not directory.is_dir():
            continue
        found = artifacts(directory)
        if not found:
            continue
        # The address of the population is the address of its addresses. Any artifact added,
        # removed, or altered moves it; nothing else does.
        rolled = hashlib.sha256()
        for address, _, path in found:
            rolled.update(address.encode())
            rolled.update(path.encode())
        extent = sum(size for _, size, _ in found)
        rows.append((rolled.hexdigest(), len(found), extent, str(directory.relative_to(ROOT))))
    return rows


def read_manifest() -> list[tuple[str, int, int, str]]:
    if not MANIFEST.exists():
        return []
    rows: list[tuple[str, int, int, str]] = []
    for line in MANIFEST.read_text().splitlines():
        if not line or line.startswith("#") or line == HEADER:
            continue
        address, returns, extent, path = line.split("\t", 3)
        rows.append((address, int(returns), int(extent), path))
    return rows


def write_manifest(rows: list[tuple[str, int, int, str]]) -> None:
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    total = sum(extent for _, _, extent, _ in rows)
    returned = sum(count for _, count, _, _ in rows)
    body = [
        "# Content addresses of the returns under `output/`, which git does not track.",
        "# One row per driver. `sha256` is taken over the sorted addresses of that driver's",
        "# artifacts, so it moves if any byte of any artifact moves.",
        "# Regenerate: python3 tools/output_manifest.py",
        "# Verify:     python3 tools/output_manifest.py --check",
        "# Listing:    python3 tools/output_manifest.py --files",
        f"# {len(rows)} drivers, {returned} returns, {total} bytes.",
        HEADER,
    ]
    body.extend(
        f"{address}\t{count}\t{extent}\t{path}" for address, count, extent, path in rows
    )
    MANIFEST.write_text("\n".join(body) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report disagreement, write nothing")
    parser.add_argument("--files", action="store_true", help="per-artifact listing, write nothing")
    arguments = parser.parse_args()

    if arguments.files:
        for directory in sorted(OUTPUT.iterdir()) if OUTPUT.is_dir() else []:
            if directory.is_dir():
                for address, extent, path in artifacts(directory):
                    print(f"{address}\t{extent}\t{path}")
        return 0

    present = survey()
    if not arguments.check:
        write_manifest(present)
        total = sum(extent for _, _, extent, _ in present)
        returned = sum(count for _, count, _, _ in present)
        print(
            f"{len(present)} drivers, {returned} returns, {total} bytes"
            f" -> {MANIFEST.relative_to(ROOT)}"
        )
        return 0

    recorded = read_manifest()
    by_path_recorded = {path: (address, count, extent) for address, count, extent, path in recorded}
    by_path_present = {path: (address, count, extent) for address, count, extent, path in present}

    # A departed driver is the loss this file exists to make reportable; a moved one returned
    # something different without its manifest; an unrecorded one is a return nothing can cite.
    departed = sorted(set(by_path_recorded) - set(by_path_present))
    unrecorded = sorted(set(by_path_present) - set(by_path_recorded))
    moved = sorted(
        path
        for path in set(by_path_recorded) & set(by_path_present)
        if by_path_recorded[path] != by_path_present[path]
    )

    for path in departed:
        print(f"DEPARTED    {by_path_recorded[path][0][:16]}  {path}")
    for path in moved:
        print(f"MOVED       {by_path_present[path][0][:16]}  {path}")
    for path in unrecorded:
        print(f"UNRECORDED  {by_path_present[path][0][:16]}  {path}")

    print(
        f"recorded {len(recorded)} drivers, present {len(present)}: "
        f"{len(departed)} departed, {len(moved)} moved, {len(unrecorded)} unrecorded"
    )
    return 1 if (departed or moved or unrecorded) else 0


if __name__ == "__main__":
    sys.exit(main())
