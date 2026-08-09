#!/usr/bin/env python3
"""Bind every returned artifact under `output/` to its content hash, in a TRACKED file.

`.gitignore` says it in its own first lines: *"A driver writes its returns under `/output/`. That
directory is ignored, and an ignored `/output/` is a return the repository cannot certify and can
lose."* The repository knew, said so, and lost evidence to that sink anyway — the residue-stratum
atlas is under `output/` on disk right now with no commit behind it, and the tiger phase atlas went
the same way through `target/`.

This does not track the artifacts. Tracking 210 MB of driver returns would be wrong. It tracks the
one thing that makes a loss *detectable and reportable*: the address.

    python3 tools/output_manifest.py           # rewrite meta/OUTPUT_MANIFEST.tsv
    python3 tools/output_manifest.py --check    # exit 1 if the tree disagrees with the manifest

`CLAUDE.md` §0 lesson 1: *"Bind every deposit to its content hash AND its closure hash, with a
verifier."* This is the content half. The closure half still has no owner.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "output"
MANIFEST = ROOT / "meta" / "OUTPUT_MANIFEST.tsv"
HEADER = "sha256\tbytes\tpath"


def digest(path: Path) -> tuple[str, int]:
    """Content address and extent. Streamed — driver returns reach hundreds of megabytes."""
    accumulator = hashlib.sha256()
    extent = 0
    with path.open("rb") as handle:
        while chunk := handle.read(1 << 20):
            accumulator.update(chunk)
            extent += len(chunk)
    return accumulator.hexdigest(), extent


def survey() -> list[tuple[str, int, str]]:
    """Every regular file under `output/`, in one canonical order so the manifest is diffable."""
    if not OUTPUT.is_dir():
        return []
    rows: list[tuple[str, int, str]] = []
    for path in sorted(OUTPUT.rglob("*")):
        if not path.is_file() or path.is_symlink():
            continue
        address, extent = digest(path)
        rows.append((address, extent, str(path.relative_to(ROOT))))
    return rows


def read_manifest() -> list[tuple[str, int, str]]:
    if not MANIFEST.exists():
        return []
    rows: list[tuple[str, int, str]] = []
    for line in MANIFEST.read_text().splitlines():
        if not line or line.startswith("#") or line == HEADER:
            continue
        address, extent, path = line.split("\t", 2)
        rows.append((address, int(extent), path))
    return rows


def write_manifest(rows: list[tuple[str, int, str]]) -> None:
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    total = sum(extent for _, extent, _ in rows)
    body = [
        "# Content addresses of the returns under `output/`, which git does not track.",
        "# Regenerate: python3 tools/output_manifest.py",
        "# Verify:     python3 tools/output_manifest.py --check",
        f"# {len(rows)} artifacts, {total} bytes.",
        HEADER,
    ]
    body.extend(f"{address}\t{extent}\t{path}" for address, extent, path in rows)
    MANIFEST.write_text("\n".join(body) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report disagreement, write nothing")
    arguments = parser.parse_args()

    present = survey()
    if not arguments.check:
        write_manifest(present)
        total = sum(extent for _, extent, _ in present)
        print(f"{len(present)} artifacts, {total} bytes -> {MANIFEST.relative_to(ROOT)}")
        return 0

    recorded = read_manifest()
    by_path_recorded = {path: (address, extent) for address, extent, path in recorded}
    by_path_present = {path: (address, extent) for address, extent, path in present}

    # A departed artifact is the loss this file exists to make reportable; a changed one is a
    # return that moved without its manifest; an unrecorded one is a return nothing can cite.
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
        f"recorded {len(recorded)}, present {len(present)}: "
        f"{len(departed)} departed, {len(moved)} moved, {len(unrecorded)} unrecorded"
    )
    return 1 if (departed or moved or unrecorded) else 0


if __name__ == "__main__":
    sys.exit(main())
