#!/usr/bin/env python3
"""Bind every return under `output/` to the CLOSURE that produced it, not only to its content.

`CLAUDE.md` §0 lesson 1, whole: *"Bind every deposit to its content hash **AND its closure hash**,
with a verifier."* `tools/output_manifest.py` is the content half and says so in its own header —
*"The closure half still has no owner."* This is that owner.

    python3 tools/closure_manifest.py            # rewrite meta/CLOSURE_MANIFEST.tsv
    python3 tools/closure_manifest.py --check    # exit 1 if the tree disagrees with the manifest
    python3 tools/closure_manifest.py --orphans  # print returns whose producer is not in the tree

# What a closure hash is, and why the content hash cannot do its job

A content hash answers *"is this artifact the bytes it was?"*. It cannot answer *"was this artifact
produced by the code it claims to have been produced by?"* — and that is the question the two lost
probe binaries make concrete. `zz_smith_cost_probe` and `zz_torsion_width_law` ran from `target/`,
returned real cost laws, and **their sources were never committed**. Their content hashes would have
verified perfectly right up until the binaries were deleted, because a content hash of a return says
nothing about the producer of that return.

So the closure of a return is:

    the driver source that produced it
      + every workspace source file that driver's crate compiles
      + the manifest of that crate

hashed together. If any of those move, the closure hash moves, and a return whose closure hash no
longer matches is **a return the current tree cannot reproduce** — which is exactly the condition
that lost the tiger figures and the residue-stratum atlas.

# The orphan is the finding, not the error

A return under `output/` whose producing driver is **not in the tree at all** is an orphan: evidence
with no reproducible source. `--orphans` lists them and the check reports them without failing,
because an orphan is a measurement about the corpus and not a defect in this tool. **The two `zz_`
probes are orphans by construction — their returns are gone too, so they appear nowhere, and that is
the shape of the loss: it leaves no trace to find.**

# No aperture

Every driver directory under `output/` is bound, uniformly. The producing driver is located by name:
`output/<slug>/` is produced by the driver whose file stem is `<slug>` with `-` read as `_`. A
directory whose driver cannot be located is reported rather than skipped silently.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "output"
MANIFEST = ROOT / "meta" / "CLOSURE_MANIFEST.tsv"

HEADER = (
    "# Closure addresses of the returns under `output/`.\n"
    "# One row per driver. `closure` is taken over the driver source, every source file of the\n"
    "# crate it lives in, and that crate's manifest — so it moves if anything that could change\n"
    "# what the driver returns moves. `CLAUDE.md` §0 lesson 1's second half.\n"
    "# `producer` is `ORPHAN` when no driver in the tree bears the directory's name: that is a\n"
    "# return the tree cannot reproduce, and it is reported rather than skipped.\n"
    "driver\tproducer\tclosure\tsources\n"
)


def driver_sources() -> dict[str, Path]:
    """Every example driver in the workspace, keyed by its file stem."""
    found: dict[str, Path] = {}
    for crate in sorted((ROOT / "crates").glob("*/examples/*.rs")):
        found[crate.stem] = crate
    for crate in sorted((ROOT / "soma").glob("*/examples/*.rs")):
        found.setdefault(crate.stem, crate)
    return found


def crate_of(source: Path) -> Path:
    """The crate root a driver belongs to — the directory holding its `Cargo.toml`."""
    for parent in source.parents:
        if (parent / "Cargo.toml").is_file():
            return parent
    return source.parent


@lru_cache(maxsize=None)
def file_digest(source: Path) -> str:
    """Hash a source occurrence once per manifest reading."""

    return hashlib.sha256(source.read_bytes()).hexdigest()


@lru_cache(maxsize=None)
def crate_members(crate: Path) -> tuple[Path, ...]:
    """The shared closure population of a driver-owning crate, founded once per crate."""

    members = [crate / "Cargo.toml"]
    members += sorted((crate / "src").rglob("*.rs"))
    return tuple(member for member in sorted(set(members)) if member.is_file())


def closure_of(source: Path) -> tuple[str, int]:
    """Hash the driver, its crate's sources, and its crate manifest. Returns (hash, file count)."""
    crate = crate_of(source)
    members = [source, *crate_members(crate)]
    digest = hashlib.sha256()
    counted = 0
    for member in sorted(set(members)):
        if not member.is_file():
            continue
        digest.update(str(member.relative_to(ROOT)).encode())
        digest.update(b"\0")
        digest.update(file_digest(member).encode())
        digest.update(b"\n")
        counted += 1
    return digest.hexdigest(), counted


def rows() -> list[tuple[str, str, str, int]]:
    if not OUTPUT.is_dir():
        return []
    drivers = driver_sources()
    built: list[tuple[str, str, str, int]] = []
    for directory in sorted(p for p in OUTPUT.iterdir() if p.is_dir()):
        slug = directory.name
        candidate = drivers.get(slug) or drivers.get(slug.replace("-", "_"))
        if candidate is None:
            built.append((slug, "ORPHAN", "-", 0))
            continue
        digest, counted = closure_of(candidate)
        built.append((slug, str(candidate.relative_to(ROOT)), digest, counted))
    return built


def render(built: list[tuple[str, str, str, int]]) -> str:
    body = "".join(f"{slug}\t{producer}\t{digest}\t{count}\n" for slug, producer, digest, count in built)
    return HEADER + body


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 if the manifest is stale")
    parser.add_argument("--orphans", action="store_true", help="list returns with no producer")
    arguments = parser.parse_args()

    built = rows()

    if arguments.orphans:
        orphans = [slug for slug, producer, _, _ in built if producer == "ORPHAN"]
        for slug in orphans:
            print(f"ORPHAN  output/{slug}  — no driver in the tree bears this name")
        print(f"{len(orphans)} orphan(s) of {len(built)} return directories")
        return 0

    rendered = render(built)

    if arguments.check:
        if not MANIFEST.is_file():
            print(f"missing {MANIFEST.relative_to(ROOT)}; run without --check to write it")
            return 1
        carried = MANIFEST.read_text()
        if carried != rendered:
            print(f"{MANIFEST.relative_to(ROOT)} disagrees with the tree")
            carried_rows = {line.split("\t")[0]: line for line in carried.splitlines() if "\t" in line}
            for slug, producer, digest, count in built:
                line = f"{slug}\t{producer}\t{digest}\t{count}"
                if carried_rows.get(slug) != line:
                    print(f"  moved: {slug}")
            return 1
        orphans = sum(1 for _, producer, _, _ in built if producer == "ORPHAN")
        print(f"closure manifest current: {len(built)} return directories, {orphans} orphan(s)")
        return 0

    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(rendered)
    orphans = sum(1 for _, producer, _, _ in built if producer == "ORPHAN")
    print(f"wrote {MANIFEST.relative_to(ROOT)}: {len(built)} return directories, {orphans} orphan(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
