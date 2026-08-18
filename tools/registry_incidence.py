#!/usr/bin/env python3
"""Emit the registry-to-code incidence as a TSV.

The falsifier standing in `CONSTRUCTION_STATE.md` since 2026-08-07 asks that
`crates/holonic-engine/src/receiver_exact_compression.rs` return the same *kind* of artifact — a
counted, exhibitable collapsed population with the shortest separating context — **on materially
unrelated sources**, and that the shapes differ. This supplies one such source: the registry's own
dependency graph, with each entry's grade and whether any Rust file cites it.

It is deliberately a generator rather than a hand-written fixture, so the material cannot be
authored to produce a pleasing partition. Run it before the driver that consumes it.

    python3 tools/registry_incidence.py            # writes meta/REGISTRY_INCIDENCE.tsv
    python3 tools/registry_incidence.py --check    # non-zero if the ledger has drifted
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "papers" / "source" / "holonics"
LEDGER = ROOT / "meta" / "REGISTRY_INCIDENCE.tsv"

ENTRY = re.compile(r'\bid:\s*"((?:H|RH|C)\.\d{4})"')
GRADE = re.compile(r'\bgrade:\s*"([a-z-]+)"')
DEPENDS = re.compile(r"\bdepends:\s*\(([^)]*)\)", re.S)
DEPENDENCY = re.compile(r'"((?:H|RH|C)\.\d{4})"')


def entries() -> list[dict[str, str]]:
    """Every registry entry, with its grade and its declared dependencies."""
    found: list[dict[str, str]] = []
    for path in sorted(REGISTRY.glob("*.typ")):
        text = path.read_text(encoding="utf-8")
        for match in ENTRY.finditer(text):
            # The entry's own body runs to the next `id:` or the end of the file.
            following = ENTRY.search(text, match.end())
            body = text[match.end() : following.start() if following else len(text)]
            grade = GRADE.search(body)
            depends = DEPENDS.search(body)
            found.append(
                {
                    "id": match.group(1),
                    "file": path.name,
                    "grade": grade.group(1) if grade else "none",
                    "depends": ";".join(
                        DEPENDENCY.findall(depends.group(1)) if depends else []
                    ),
                }
            )
    return found


def cited_from_rust() -> set[str]:
    """Every registry id named in a Rust source file."""
    try:
        found = subprocess.run(
            ["grep", "-rhoE", r"(H|RH|C)\.[0-9]{4}", "--include=*.rs", "crates", "soma"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return set()
    return {line.strip() for line in found.stdout.splitlines() if line.strip()}


def render() -> str:
    cited = cited_from_rust()
    rows = ["\t".join(("id", "file", "grade", "cited_from_rust", "depends"))]
    for entry in entries():
        rows.append(
            "\t".join(
                (
                    entry["id"],
                    entry["file"],
                    entry["grade"],
                    "1" if entry["id"] in cited else "0",
                    entry["depends"],
                )
            )
        )
    return "\n".join(rows) + "\n"


def main() -> int:
    rendered = render()
    if "--check" in sys.argv:
        if not LEDGER.exists() or LEDGER.read_text(encoding="utf-8") != rendered:
            print("registry incidence ledger has drifted; re-run without --check")
            return 1
        print("registry incidence current")
        return 0
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    LEDGER.write_text(rendered, encoding="utf-8")
    total = rendered.count("\n") - 1
    cited = sum(1 for line in rendered.splitlines()[1:] if line.split("\t")[3] == "1")
    print(f"wrote {LEDGER.relative_to(ROOT)}: {total} entries, {cited} cited from Rust")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
