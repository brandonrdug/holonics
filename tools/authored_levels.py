#!/usr/bin/env python3
"""Every numeric level authored **inside** an organ, and whether it is dispositioned.

`CLAUDE.md` and the roadmap have discovered pinned constants one at a time for weeks — a call site
that fixes `characteristic_delay: 1`, a `LEADER_WITNESS_DEPTH: usize = 1`, a `REFINEMENT_APERTURE`
of 64 — each found by hand, each reported as though it were the last one. Brandon, 2026-08-09, on
that loop: *"you will keep saying things like 'that is the same law one level down', when the fact
is that we already know how the network needs to work, and that **we are not the ones meant to be
pinning levels to minimums and maximums**."*

This makes it mechanical. **The law it enforces:**

> A level is either **read off the material** or **declared by the caller**. It is never authored
> inside the organ.

The tool cannot decide which of those a constant is — that is a reading. What it *can* do is
enumerate every authored numeric level in library code and require each to carry an explicit
disposition in `meta/AUTHORED_LEVELS.tsv`. An undispositioned constant fails the run, so a new pin
is visible the day it lands rather than in a hand audit six weeks later.

    python3 tools/authored_levels.py            # report, and list what is undispositioned
    python3 tools/authored_levels.py --check    # exit 1 if anything is undispositioned or stale
    python3 tools/authored_levels.py --write    # seed the registry with what is present

**Dispositions**, and each carries a burden of proof:

    MATERIAL   a fact of the mathematics that cannot vary. Must name the theorem in `why`.
               `QUADRIC_COEFFICIENT_COUNT = 10` is NOT this: a quadric in n variables has
               C(n+2,2) coefficients, so 10 pins n = 3 and the name hides it.
    ABI        a hardware, wire-format or foreign-interface constant. `CUDA_SUCCESS = 0`.
    APERTURE   declared, RETURNS ITS OUTSIDE, and `why` must state what it would take to derive
               the level from the material. Refusing past a number you invented does not make the
               number derived; the `why` is what keeps that honest.
    PIN        a contaminant. `why` must carry the excision plan.

Scope is **library code only** — `crates/*/src`, `soma/*/src`. Drivers and tests declare their own
material and are the right place for a literal.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "meta" / "AUTHORED_LEVELS.tsv"
HEADER = "disposition\towner\tname\tvalue\twhy"

DISPOSITIONS = {"MATERIAL", "ABI", "APERTURE", "PIN"}

# A numeric const declared in an organ. Sizes, tags and layout words are excluded by name below.
CONST = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+([A-Z][A-Z0-9_]*)\s*:\s*"
    r"(?:usize|isize|u8|u16|u32|u64|u128|i8|i16|i32|i64|i128)\s*=\s*"
    r"([0-9][0-9_]*)\s*;"
)

# Names that are not levels: wire tags, layout widths, schema versions, and the carrier's own word.
NOT_A_LEVEL = re.compile(
    r"(TAG|MAGIC|SCHEMA|VERSION|_LO$|_HI$|WORDS$|_BITS$|OCTETS?$|BYTES?$|SUCCESS$|"
    r"LAYOUT|OFFSET|STRIDE|ALIGN)",
    re.IGNORECASE,
)


def library_sources() -> list[Path]:
    """Library code only. A driver's literal is a declared fixture, not an authored level."""
    found: list[Path] = []
    for crate in sorted((ROOT / "crates").glob("*/src")):
        found.extend(sorted(crate.rglob("*.rs")))
    for organ in sorted((ROOT / "soma").glob("*/src")):
        found.extend(sorted(organ.rglob("*.rs")))
    # Test bodies and mount gates declare their own fixtures; a literal there is material, not a
    # level authored into an organ.
    return [
        path
        for path in found
        if "/tests" not in str(path)
        and not path.stem.endswith("_tests")
        and not path.stem.startswith("mount-")
        and not path.stem.endswith("-gate")
    ]


def present() -> list[tuple[str, str, str]]:
    """Every authored numeric level in library code: (owner, name, value)."""
    found: list[tuple[str, str, str]] = []
    for path in library_sources():
        try:
            text = path.read_text()
        except OSError:
            continue
        in_test = False
        depth = 0
        for line in text.splitlines():
            # A `#[cfg(test)]` module owns its own material — and the exclusion must END where that
            # module does. Until 2026-08-09 `in_test` was set once and never reset, so every const
            # after the FIRST test module in a file was invisible: 58 levels tree-wide, 13 of them in
            # the language body, including `CODEC_MINIMUM_RECURRENCE` and `CODEC_TEMPLATE_APERTURE`
            # at `soma/life/src/agentic_language.rs:65-66`, which sit ten lines below the
            # `#[cfg(test)]` at `:55` and decide when a correction becomes generative.
            #
            # `canon/THE_AUTHORED_LEVEL.md` already says the tool is a convenience and never the
            # authority — *"a level its regex does not match is exactly as much a contaminant as one
            # it does"* — and this was that failure in its own scanner, reporting `0 failures` over a
            # population it could not see.
            if line.strip().startswith("#[cfg(test)]"):
                in_test = True
                depth = 0
            if in_test:
                depth += line.count("{") - line.count("}")
                if depth <= 0 and "}" in line:
                    in_test = False
                continue
            matched = CONST.match(line)
            if not matched:
                continue
            name, value = matched.group(1), matched.group(2)
            if NOT_A_LEVEL.search(name):
                continue
            found.append((str(path.relative_to(ROOT)), name, value.replace("_", "")))
    return sorted(found)


def read_registry() -> dict[tuple[str, str], tuple[str, str, str]]:
    if not REGISTRY.exists():
        return {}
    carried: dict[tuple[str, str], tuple[str, str, str]] = {}
    for line in REGISTRY.read_text().splitlines():
        if not line or line.startswith("#") or line == HEADER:
            continue
        disposition, owner, name, value, why = line.split("\t", 4)
        carried[(owner, name)] = (disposition, value, why)
    return carried


def write_registry(rows: list[tuple[str, str, str, str, str]]) -> None:
    REGISTRY.parent.mkdir(parents=True, exist_ok=True)
    body = [
        "# Every numeric level authored inside a library organ, with its disposition.",
        "#",
        "# THE LAW: a level is either read off the material or declared by the caller. It is never",
        "# authored inside the organ. See canon/THE_AUTHORED_LEVEL.md.",
        "#",
        "# MATERIAL  a fact that cannot vary; `why` names the theorem.",
        "# ABI       hardware, wire format, or foreign interface.",
        "# APERTURE  declared, returns its outside, and `why` states what would derive it.",
        "# PIN       a contaminant; `why` carries the excision plan.",
        "#",
        "# Regenerate: python3 tools/authored_levels.py --write",
        "# Verify:     python3 tools/authored_levels.py --check",
        HEADER,
    ]
    body.extend("\t".join(row) for row in rows)
    REGISTRY.write_text("\n".join(body) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 on anything undispositioned")
    parser.add_argument("--write", action="store_true", help="seed the registry from the tree")
    arguments = parser.parse_args()

    found = present()
    carried = read_registry()

    undispositioned = [(owner, name, value) for owner, name, value in found if (owner, name) not in carried]
    moved = [
        (owner, name, value, carried[(owner, name)][1])
        for owner, name, value in found
        if (owner, name) in carried and carried[(owner, name)][1] != value
    ]
    departed = sorted(set(carried) - {(owner, name) for owner, name, _ in found})

    if arguments.write:
        rows = []
        for owner, name, value in found:
            disposition, _, why = carried.get((owner, name), ("PIN", "", "UNDISPOSITIONED"))
            rows.append((disposition, owner, name, value, why))
        write_registry(rows)
        print(f"{len(rows)} authored levels -> {REGISTRY.relative_to(ROOT)}")
        return 0

    by_disposition: dict[str, int] = {}
    for owner, name, _ in found:
        disposition = carried.get((owner, name), ("UNDISPOSITIONED",))[0]
        by_disposition[disposition] = by_disposition.get(disposition, 0) + 1

    print(f"{len(found)} authored numeric levels in library code")
    for disposition in sorted(by_disposition):
        print(f"  {disposition:<16} {by_disposition[disposition]}")

    for owner, name, value in undispositioned:
        print(f"UNDISPOSITIONED  {owner}  {name} = {value}")
    for owner, name, value, was in moved:
        print(f"MOVED            {owner}  {name}: {was} -> {value}")
    for owner, name in departed:
        print(f"DEPARTED         {owner}  {name}")

    bad = [d for d in by_disposition if d not in DISPOSITIONS]
    for disposition in bad:
        print(f"UNKNOWN DISPOSITION  {disposition}")

    if arguments.check:
        failures = len(undispositioned) + len(moved) + len(departed) + len(bad)
        print(f"\n{failures} failures")
        return 1 if failures else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
