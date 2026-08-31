#!/usr/bin/env python3
"""Generate `meta/DRIVER_CATALOG.tsv` from the tree, so the driver population cannot go uncatalogued.

    python3 tools/driver_catalog.py            # rewrite meta/DRIVER_CATALOG.tsv
    python3 tools/driver_catalog.py --check    # exit 1 if the ledger disagrees with the tree
    python3 tools/driver_catalog.py --self-test # synthetic Cargo-target/helper control

# Why this exists

Measured 2026-08-16 by `find crates soma -path '*/examples/*.rs'`: **203 example drivers, 163,332
lines — 42% the size of every library crate combined — accrued over ten days.** Measured the same
hour: **0** of them appear in `THE_CLAIM_INDEX.md`, **41** are named in no document under `canon/`,
`blueprint/`, `research/`, `meta/`, `tools/` or the repository root, and **90** share an *identical*
library-import set with at least one other driver. There was no catalog of any kind.

Brandon, the same hour: *"The point of the drivers is not to produce them and leave them as
examples, they are just partials that need to unify into the Information Engine/Eros cycle… I don't
know if you've consolidated the abstractions of what each driver actually does in its experiment and
why we ever bothered making it an independent example driver."*

The consequence is not tidiness. A driver nobody can find is a **capability nobody can cite**, so the
same mechanism gets rebuilt beside its own prior implementation — which is exactly the explorative
failure `canon/THE_EXPLORATIVE_FAILURE.md` names, with the driver population as its habitat. Two
drivers written on consecutive days in this very session share an identical import set and run the
same organ over prose.

# What this tool does and does not claim

**Every column here is a measurement over the tree and nothing here is a reading.** The tool cannot
say what a driver *showed*; that is `canon/THE_DRIVER_ATLAS.md`, which is written by hand and cites
this ledger. What this tool guarantees is that no driver is missing from the catalog and no catalog
row names a driver that is gone.

The `exterior` column is measured over **code**, with `//` line comments and `//!` module docs
stripped first, because a driver that merely discusses the card in prose has not reached it. It
records which exterior the driver's code actually reaches:

    kernel      a subprocess is spawned — an exterior that returns a verdict this body did not author
    card        a CUDA carrier type is constructed or a kernel module is loaded
    deposit     bytes leave the process into the filesystem
    none        the driver mounts material, computes, and prints

`none` is not a defect on its own. It is the measurement that separates an **instrument reading**
from a closed cycle, and `canon/THE_INFORMATION_ENGINE.md` is the authority on which is which:
emission and return are distinct caused occurrences joined by addressed lineage, and a private echo
is not a return.

The `named_in` column counts governing documents and research records that name the driver's
basename. It measures **naming, not execution** — the same bound `THE_CLAIM_INDEX.md` states about
its own gate column.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "meta" / "DRIVER_CATALOG.tsv"

# Cargo metadata owns driver discovery. A recursive `examples/**/*.rs` walk confuses target roots
# with their nested modules; a fixed-depth glob misses explicitly declared nested targets. Both
# defects are eliminated by consuming Cargo's target graph.

# Where a driver may be NAMED. `tools/` is included because a gate that runs a driver names it.
NAMING_ROOTS = ("canon", "blueprint", "research", "meta", "tools", "papers")
NAMING_SUFFIXES = (".md", ".tsv", ".sh", ".py", ".typ", ".toml")

# The library crates and soma members whose modules a driver may drive. A driver's owner set is the
# strongest cheap signal of duplication: two drivers reaching for exactly the same owners are asking
# related questions whatever their filenames say.
OWNER_ROOTS = (
    "holonic_engine",
    "holonic_structure",
    "holonic_language",
    "relational_geometry",
    "life",
    "body",
    "soma_abi",
    "soma_membrane",
    "soma_mount",
    "soma_surface",
    "soma_formal",
)

FIELDS = (
    "driver",
    "target",
    "crate",
    "lines",
    "owners",
    "declared_source",
    "exterior",
    "output_manifest",
    "closure_manifest",
    "named_in",
    "subject",
)

METADATA_TIMEOUT_SECONDS = 175


def cargo_metadata(root: Path) -> dict[str, object]:
    """Return Cargo's target graph without compiling a target.

    Cargo, rather than a recursive filename walk, owns the distinction between an example target
    and a Rust module stored below ``examples/``.  ``--no-deps`` is sufficient here because the
    catalog needs target declarations, not the dependency closure.
    """

    try:
        completed = subprocess.run(
            [
                "cargo",
                "metadata",
                "--format-version",
                "1",
                "--no-deps",
            ],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
            timeout=METADATA_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(
            f"cargo metadata exceeded {METADATA_TIMEOUT_SECONDS} seconds"
        ) from error
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise RuntimeError(f"cargo metadata failed: {detail}")
    try:
        payload = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"cargo metadata returned invalid JSON: {error}") from error
    if not isinstance(payload, dict):
        raise RuntimeError("cargo metadata did not return a JSON object")
    return payload


def example_targets(root: Path = ROOT) -> list[tuple[str, Path, Path]]:
    """Return ``(target name, source, crate root)`` for every real Cargo example target."""

    root = root.resolve()
    targets: list[tuple[str, Path, Path]] = []
    for package in cargo_metadata(root).get("packages", []):
        if not isinstance(package, dict):
            continue
        manifest = Path(str(package["manifest_path"])).resolve()
        crate = manifest.parent
        for target in package.get("targets", []):
            if not isinstance(target, dict) or "example" not in target.get("kind", []):
                continue
            source = Path(str(target["src_path"])).resolve()
            try:
                source.relative_to(root)
                crate.relative_to(root)
            except ValueError as error:
                raise RuntimeError(
                    f"Cargo example target {target.get('name')!r} is outside {root}"
                ) from error
            if not source.is_file():
                raise RuntimeError(
                    f"Cargo example target {target.get('name')!r} has no source at {source}"
                )
            targets.append((str(target["name"]), source, crate))
    targets.sort(key=lambda item: (str(item[1]), item[0]))
    return targets


def strip_comments(source: str) -> str:
    """Remove `//!` docs and `//` line comments. A mention in prose is not a reach."""
    out = []
    for line in source.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("//"):
            continue
        at = line.find("//")
        out.append(line[:at] if at >= 0 else line)
    return "\n".join(out)


def subject_of(source: str) -> str:
    """The driver's own declared subject: the first `//!` line, which by house style is a title.

    Copied, never summarized — the same discipline `tools/claim_index.py` runs on documents.
    """
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped.startswith("//!"):
            if stripped.startswith(("use ", "#!", "#[")) or stripped.startswith("fn "):
                break
            continue
        text = stripped[3:].strip()
        if not text:
            continue
        # House style puts the title on the first doc line, often followed by ` — gloss`.
        return re.sub(r"\s+", " ", text).rstrip(".")
    return ""


def owners_of(code: str) -> list[str]:
    """Every library module the driver's code imports, as `crate::module`, sorted and unique."""
    found: set[str] = set()
    for root in OWNER_ROOTS:
        for match in re.finditer(rf"\b{root}::([a-z_][a-z0-9_]*)", code):
            found.add(f"{root}::{match.group(1)}")
        # A bare `use life::{a, b};` names its modules inside the brace.
        for match in re.finditer(rf"use\s+{root}::\{{([^}}]*)\}}", code, re.S):
            for piece in match.group(1).split(","):
                name = piece.strip().split("::")[0].strip()
                if re.fullmatch(r"[a-z_][a-z0-9_]*", name):
                    found.add(f"{root}::{name}")
    return sorted(found)


def exterior_of(code: str) -> str:
    """Which exterior the driver's CODE reaches. Prose mentions are already stripped."""
    reached = []
    if re.search(r"\bCommand::new\b", code):
        reached.append("kernel")
    if re.search(r"\bCuda[A-Z]\w*\b|\bcuda::", code):
        reached.append("card")
    if re.search(r"\bfs::write\b|\bdeposit_form\w*\b|\bFile::create\b", code):
        reached.append("deposit")
    return "+".join(reached) if reached else "none"


def takes_declared_source(code: str) -> str:
    """Does the driver refuse without a caller-declared input? Measured on its argument handling."""
    if re.search(r"env::args(_os)?\(\)", code):
        return "yes"
    return "no"


def manifest_membership() -> tuple[set[str], set[str]]:
    def read(path: Path) -> set[str]:
        if not path.exists():
            return set()
        names: set[str] = set()
        for line in path.read_text().splitlines()[1:]:
            for cell in line.split("\t"):
                cell = cell.strip()
                if cell:
                    names.add(Path(cell).stem)
                    names.add(cell)
        return names

    return (
        read(ROOT / "meta" / "OUTPUT_MANIFEST.tsv"),
        read(ROOT / "meta" / "CLOSURE_MANIFEST.tsv"),
    )


def naming_corpus() -> list[str]:
    texts = []
    for root in NAMING_ROOTS:
        base = ROOT / root
        if not base.is_dir():
            continue
        for path in base.rglob("*"):
            if path.is_file() and path.suffix in NAMING_SUFFIXES:
                if path == LEDGER:
                    continue
                try:
                    texts.append(path.read_text(errors="ignore"))
                except OSError:
                    pass
    for path in ROOT.glob("*.md"):
        texts.append(path.read_text(errors="ignore"))
    return texts


def rows(root: Path = ROOT) -> list[dict[str, str]]:
    output_names, closure_names = manifest_membership()
    corpus = naming_corpus()
    collected = []
    for target_name, path, crate in example_targets(root):
        source = path.read_text(errors="ignore")
        code = strip_comments(source)
        stem = path.stem
        named = sum(1 for text in corpus if stem in text or target_name in text)
        collected.append(
            {
                "driver": str(path.relative_to(root)),
                "target": target_name,
                "crate": str(crate.relative_to(root)),
                "lines": str(len(source.splitlines())),
                "owners": ";".join(owners_of(code)) or "-",
                "declared_source": takes_declared_source(code),
                "exterior": exterior_of(code),
                "output_manifest": (
                    "yes" if stem in output_names or target_name in output_names else "no"
                ),
                "closure_manifest": (
                    "yes" if stem in closure_names or target_name in closure_names else "no"
                ),
                "named_in": str(named),
                "subject": subject_of(source) or "-",
            }
        )
    return collected


def self_test() -> None:
    """Prove that Cargo targets enter while nested helper modules do not become drivers."""

    with tempfile.TemporaryDirectory(prefix="holonics-driver-catalog-") as temporary:
        root = Path(temporary)
        (root / "src").mkdir()
        (root / "examples" / "support").mkdir(parents=True)
        (root / "examples" / "nested").mkdir(parents=True)
        (root / "Cargo.toml").write_text(
            """[package]
name = "catalog-control"
version = "0.0.0"
edition = "2021"

[[example]]
name = "nested-target"
path = "examples/nested/main.rs"
""",
            encoding="utf-8",
        )
        (root / "src" / "lib.rs").write_text("pub fn standing() {}\n", encoding="utf-8")
        (root / "examples" / "visible.rs").write_text("fn main() {}\n", encoding="utf-8")
        (root / "examples" / "nested" / "main.rs").write_text(
            "fn main() {}\n", encoding="utf-8"
        )
        (root / "examples" / "support" / "helper.rs").write_text(
            "pub fn helper() {}\n", encoding="utf-8"
        )
        returned = example_targets(root)
        names = [name for name, _, _ in returned]
        paths = [str(path.relative_to(root)) for _, path, _ in returned]
        assert names == ["nested-target", "visible"], names
        assert "examples/support/helper.rs" not in paths, paths
        print(
            "driver-catalog self-test: 2 Cargo example targets; "
            "nested helper is not a driver"
        )


def render(collected: list[dict[str, str]]) -> str:
    lines = ["\t".join(FIELDS)]
    for row in collected:
        lines.append("\t".join(row[field].replace("\t", " ") for field in FIELDS))
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 if the ledger has drifted")
    parser.add_argument(
        "--self-test", action="store_true", help="run the synthetic Cargo-target control"
    )
    arguments = parser.parse_args()

    if arguments.self_test:
        self_test()
        return 0

    try:
        collected = rows()
    except RuntimeError as error:
        print(f"driver-catalog: {error}", file=sys.stderr)
        return 2
    rendered = render(collected)

    if arguments.check:
        if not LEDGER.exists():
            print(f"driver-catalog: {LEDGER.relative_to(ROOT)} does not exist")
            return 1
        standing = LEDGER.read_text()
        if standing == rendered:
            uncatalogued = 0
            print(f"driver-catalog: {len(collected)} drivers catalogued, {uncatalogued} uncatalogued")
            return 0
        standing_names = {line.split("\t")[0] for line in standing.splitlines()[1:]}
        tree_names = {row["driver"] for row in collected}
        added = sorted(tree_names - standing_names)
        gone = sorted(standing_names - tree_names)
        changed = len(collected) - len(added)
        print(
            f"driver-catalog: DRIFTED — {len(added)} driver(s) not in the catalog, "
            f"{len(gone)} catalogued driver(s) not in the tree, {changed} row(s) re-measured"
        )
        for name in added[:20]:
            print(f"  uncatalogued  {name}")
        for name in gone[:20]:
            print(f"  departed      {name}")
        print("  regenerate with: python3 tools/driver_catalog.py")
        return 1

    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    LEDGER.write_text(rendered)
    exteriors: dict[str, int] = {}
    for row in collected:
        exteriors[row["exterior"]] = exteriors.get(row["exterior"], 0) + 1
    unnamed = sum(1 for row in collected if row["named_in"] == "0")
    unsubjected = sum(1 for row in collected if row["subject"] == "-")
    print(f"driver-catalog: wrote {LEDGER.relative_to(ROOT)} — {len(collected)} drivers")
    print("  exterior reached: " + ", ".join(f"{k} {v}" for k, v in sorted(exteriors.items())))
    print(f"  named in no governing document or record: {unnamed}")
    # A driver with no `//!` line has not said what it is. It cannot be catalogued by its own
    # words, only by reading it, which is the cost this whole ledger exists to stop paying twice.
    print(f"  carrying no module doc, so declaring no subject: {unsubjected}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
