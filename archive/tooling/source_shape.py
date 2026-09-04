#!/usr/bin/env python3
"""Rust/CUDA source-shape gate.

Existing files may shrink but may not grow past the committed baseline in lines, public items, or
CUDA kernel entries. New Rust/CUDA owner files must begin below explicit review apertures; splitting
a hidden foreman into owner-local files is therefore admitted while moving it unchanged into one
new giant file is not.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "tools/baselines" / "SOURCE_SHAPE_BASELINE.tsv"
RUST_NEW_LINE_LIMIT = 1500
CUDA_NEW_LINE_LIMIT = 2000
NEW_PUBLIC_ITEM_LIMIT = 50
NEW_KERNEL_LIMIT = 40

PUBLIC_ITEM = re.compile(
    r"^\s*pub(?:\([^)]*\))?\s+(?:unsafe\s+)?(?:struct|enum|trait|type|fn|const|static|mod)\b",
    re.MULTILINE,
)
CUDA_KERNEL = re.compile(r'^\s*extern\s+"C"\s+__global__\s+void\s+', re.MULTILINE)


@dataclass(frozen=True)
class Shape:
    lines: int
    public_items: int
    kernels: int


def relevant(path: str) -> bool:
    if path.endswith(".rs"):
        # These exact ABI roots were outside the original soma/{life,body,membrane,mount,surface}
        # aperture. Relocation preserves that scope; their wire/layout tests remain mandatory.
        # Do not turn moving an unchanged ABI into a new public-item limit or raise a baseline.
        if path.startswith(("crates/holonic-abi/", "crates/holonic-circulation-abi/")):
            return False
        return bool(re.match(r"^crates/[^/]+/src/", path))
    if path.endswith((".cu", ".cuh")):
        return bool(re.match(r"^(?:crates/[^/]+|accelerators/[^/]+)/", path))
    return False


def shape(source: str) -> Shape:
    return Shape(
        lines=len(source.splitlines()),
        public_items=len(PUBLIC_ITEM.findall(source)),
        kernels=len(CUDA_KERNEL.findall(source)),
    )


def git(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *arguments], cwd=ROOT, text=True, capture_output=True, check=False
    )


def revision_shapes(revision: str) -> dict[str, Shape]:
    listing = git("ls-tree", "-r", "--name-only", revision)
    if listing.returncode != 0:
        raise RuntimeError(listing.stderr.strip() or f"cannot read revision {revision}")
    found: dict[str, Shape] = {}
    for path in sorted(filter(relevant, listing.stdout.splitlines())):
        returned = git("show", f"{revision}:{path}")
        if returned.returncode != 0:
            raise RuntimeError(returned.stderr.strip() or f"cannot read {revision}:{path}")
        found[path] = shape(returned.stdout)
    return found


def working_shapes() -> dict[str, Shape]:
    listing = git("ls-files", "--cached", "--others", "--exclude-standard")
    if listing.returncode != 0:
        raise RuntimeError(listing.stderr.strip() or "cannot list working sources")
    found: dict[str, Shape] = {}
    for path in sorted(filter(relevant, listing.stdout.splitlines())):
        absolute = ROOT / path
        if absolute.is_file():
            found[path] = shape(absolute.read_text(errors="replace"))
    return found


def write_baseline(rows: dict[str, Shape]) -> None:
    body = ["path\tlines\tpublic_items\tkernels"]
    body.extend(
        f"{path}\t{value.lines}\t{value.public_items}\t{value.kernels}"
        for path, value in sorted(rows.items())
    )
    BASELINE.write_text("\n".join(body) + "\n")


def read_baseline() -> dict[str, Shape]:
    if not BASELINE.is_file():
        raise RuntimeError(f"missing {BASELINE.relative_to(ROOT)}")
    found: dict[str, Shape] = {}
    for line in BASELINE.read_text().splitlines()[1:]:
        path, lines, public_items, kernels = line.split("\t")
        found[path] = Shape(int(lines), int(public_items), int(kernels))
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-baseline", metavar="REVISION")
    arguments = parser.parse_args()
    if arguments.emit_baseline:
        rows = revision_shapes(arguments.emit_baseline)
        write_baseline(rows)
        print(f"source-shape baseline: {len(rows)} files from {arguments.emit_baseline}")
        return 0

    baseline = read_baseline()
    current = working_shapes()
    violations: list[str] = []
    for path, present in current.items():
        allowed = baseline.get(path)
        if allowed is None:
            line_limit = CUDA_NEW_LINE_LIMIT if path.endswith((".cu", ".cuh")) else RUST_NEW_LINE_LIMIT
            allowed = Shape(line_limit, NEW_PUBLIC_ITEM_LIMIT, NEW_KERNEL_LIMIT)
        else:
            line_limit = CUDA_NEW_LINE_LIMIT if path.endswith((".cu", ".cuh")) else RUST_NEW_LINE_LIMIT
            allowed = Shape(
                max(allowed.lines, line_limit),
                max(allowed.public_items, NEW_PUBLIC_ITEM_LIMIT),
                max(allowed.kernels, NEW_KERNEL_LIMIT),
            )
        for field in ("lines", "public_items", "kernels"):
            observed = getattr(present, field)
            limit = getattr(allowed, field)
            if observed > limit:
                violations.append(f"{path}: {field} {observed} > {limit}")
    for violation in violations:
        print(f"SOURCE-SHAPE {violation}")
    print(
        f"source-shape: {len(current)} live files, {len(baseline)} inherited baselines, "
        f"{len(violations)} violations"
    )
    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main())
