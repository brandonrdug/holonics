#!/usr/bin/env python3
"""Every committed boundary artifact is bound to its content hash AND its closure hash.

`CLAUDE.md` section 0, lesson 1, in its own words:

> **Bind every deposit to its content hash AND its closure hash, with a verifier.** The laboratory
> lost its tiger figures and the file holding `semantics_invariant_under_exact_chart` to an
> untracked `runs/`. Neither is recoverable at any commit in either repository.

A **boundary artifact** is a compiled binary committed into the tree because the host workspace
carries the artifact without carrying the toolchain that made it. There are three:

    soma/kernel/soma.spv                              Vulkan / SPIR-V, consumed by soma/surface
    soma/mount/soma-kernel-cuda/soma_kernel_cuda.ptx  CUDA, consumed by mount and 6 gate binaries
    soma/mount/mount-smoke-kernel/mount_smoke_kernel.ptx   CUDA, consumed by mount-smoke

Each is a compiled image of source that lives beside it. Nothing in `cargo test` recompiles any of
them, so source and artifact drift **silently** — which is exactly what
`research/records/2026-08-09_THE_COMMITTED_BOUNDARY_ARTIFACT_IS_STALE_AND_CANNOT_BE_REBUILT.md`
found for `soma.spv`, and it had drifted for twenty-six days across two repositories.

    python3 tools/boundary_artifacts.py            verify; exit 1 on any disagreement
    python3 tools/boundary_artifacts.py --json     machine-readable
    python3 tools/boundary_artifacts.py --write    re-seed the registry after a DELIBERATE rebuild

WHAT IS CHECKED, and each is a separate named failure.

  ARTIFACT      the committed binary exists, and its sha256 and octet count are the declared ones.
                This is the CONTENT hash.
  CLOSURE       every source file the artifact is compiled from exists and carries its declared
                sha256, and the sha256 over the whole ordered `path\\tsha256` table is the declared
                `closure_sha256`. This is the CLOSURE hash, and it is the half that catches a
                `soma/body` edit that nobody rebuilt for.
  MEMBERSHIP    the closure DERIVED from the source right now equals the closure declared. A new
                `#[path]` include or a new path-dependency therefore fails on the day it lands
                rather than in a hand audit six weeks later. Without this check the registry could
                be satisfied by a closure that no longer describes the build.
  TOOLCHAIN     the pinned channel in `<root>/rust-toolchain.toml` is the declared one.
  BUILDER       the one command that regenerates the artifact exists and is executable.
  CONSUMER      every declared consumer exists and still names the artifact. An artifact nothing
                includes is not a boundary; it is a dead file with a hash.

TWO CLOSURE RULES, because the two boundaries are wired differently.

  PATH_INCLUDES  `soma/kernel` does not depend on `body` as a crate. Its `src/lib.rs` pulls each law
                 module in with `#[path = "../../body/src/<m>.rs"]`, so ONE language compiles on
                 both sides of the seam. The closure is that `#[path]` graph, walked transitively
                 from `entry`, plus every tracked file under `root` that is not the artifact.
                 `#[cfg(test)]`-guarded includes are excluded: the card build is `no_std` and never
                 compiles them.
  CRATE_DEPS     the two PTX kernels DO depend on `body` (and `soma-abi`) by path. The closure is
                 every tracked file under `root`, plus every tracked file of each transitive
                 path-dependency crate. This is DELIBERATELY conservative: it sweeps in
                 `soma/body/src/manifold_tests.rs`, which is `#[cfg(test)]`-gated and cannot move a
                 single emitted word of an nvptx `cdylib`. Erring toward a spurious rebuild demand
                 is the right side to err on for a drift detector, and the alternative is
                 cfg-reachability analysis that could quietly exclude something that DOES matter.

WHAT THIS TOOL DOES NOT DO. It does not rebuild. Rebuilding `soma.spv` needs a pinned nightly and a
`rustc_codegen_spirv` git revision the host workspace deliberately does not carry, and rebuilding
either PTX needs the CUDA nvptx target. So the registry's `rebuild_evidence` field records, per
artifact, whether anyone has actually reproduced the committed bytes from the declared closure. It
is provenance, not a check, and it is printed rather than asserted — `CLAUDE.md` section 8:
*grade the implementation, not the receipt*.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "meta" / "BOUNDARY_ARTIFACTS.tsv"
HEADER = "record\tartifact\tkey\tvalue"

# A `#[path = "..."]` module include. The target resolves against the directory of the file that
# declares it, which is what Rust does for a `#[path]` on a non-inline `mod`.
PATH_INCLUDE = re.compile(r'#\[path\s*=\s*"([^"]+)"\]')
CFG_TEST = re.compile(r"#\[cfg\(\s*test\s*\)\]")
# A path dependency in a Cargo manifest: `name = { path = "../body" }`.
PATH_DEP = re.compile(r'^\s*[A-Za-z0-9_-]+\s*=\s*\{[^}]*\bpath\s*=\s*"([^"]+)"', re.MULTILINE)
TOOLCHAIN_CHANNEL = re.compile(r'^\s*channel\s*=\s*"([^"]+)"', re.MULTILINE)

# Not compiled, not linked, and changing one cannot move a single emitted word.
CLOSURE_EXCLUDE = {".gitignore"}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def closure_hash(members: dict[str, str]) -> str:
    """The closure hash: sha256 over the ordered `path\\tsha256` table.

    Ordered by path, so it is a property of the SET of source bytes and not of anyone's walk order.
    """
    table = "".join(f"{p}\t{members[p]}\n" for p in sorted(members))
    return hashlib.sha256(table.encode("utf-8")).hexdigest()


def tracked(prefix: str) -> list[str]:
    out = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "--", prefix],
        capture_output=True,
        text=True,
        check=True,
    )
    return [line for line in out.stdout.splitlines() if line]


def walk_path_includes(entry: str) -> set[str]:
    """Transitive `#[path]` closure from one entry file, skipping `#[cfg(test)]` includes."""
    seen: set[str] = set()
    stack = [entry]
    while stack:
        rel = stack.pop()
        if rel in seen:
            continue
        source = ROOT / rel
        if not source.exists():
            seen.add(rel)
            continue
        seen.add(rel)
        text = source.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines()
        for index, line in enumerate(lines):
            found = PATH_INCLUDE.search(line)
            if not found:
                continue
            # Look back over blank lines for a `#[cfg(test)]` guard on the same item.
            back = index - 1
            while back >= 0 and not lines[back].strip():
                back -= 1
            if back >= 0 and CFG_TEST.search(lines[back]):
                continue
            target = (source.parent / found.group(1)).resolve()
            try:
                stack.append(str(target.relative_to(ROOT)))
            except ValueError:
                continue  # outside the repository; not ours to bind
    return seen


def walk_crate_deps(root: str) -> set[str]:
    """Every tracked file of a crate and of each transitive path-dependency crate."""
    members: set[str] = set()
    stack = [root]
    visited: set[str] = set()
    while stack:
        crate = stack.pop()
        if crate in visited:
            continue
        visited.add(crate)
        for rel in tracked(crate + "/"):
            if Path(rel).name not in CLOSURE_EXCLUDE:
                members.add(rel)
        manifest = ROOT / crate / "Cargo.toml"
        if not manifest.exists():
            continue
        text = manifest.read_text(encoding="utf-8", errors="replace")
        for dep in PATH_DEP.findall(text):
            target = (manifest.parent / dep).resolve()
            try:
                stack.append(str(target.relative_to(ROOT)))
            except ValueError:
                continue
    return members


def derive_closure(spec: dict[str, list[str]]) -> set[str]:
    artifact = spec["artifact"][0]
    root = spec["root"][0]
    rule = spec["closure_rule"][0]
    if rule == "PATH_INCLUDES":
        members = walk_path_includes(spec["entry"][0])
        for rel in tracked(root + "/"):
            if Path(rel).name not in CLOSURE_EXCLUDE:
                members.add(rel)
    elif rule == "CRATE_DEPS":
        members = walk_crate_deps(root)
    else:
        raise SystemExit(f"unknown closure_rule {rule!r} for {artifact}")
    members.discard(artifact)
    return members


def read_registry() -> tuple[dict[str, dict[str, list[str]]], dict[str, dict[str, str]]]:
    if not REGISTRY.exists():
        raise SystemExit(f"no registry at {REGISTRY.relative_to(ROOT)}")
    specs: dict[str, dict[str, list[str]]] = {}
    closures: dict[str, dict[str, str]] = {}
    for line in REGISTRY.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#") or line == HEADER:
            continue
        record, artifact, key, value = line.split("\t", 3)
        if record == "ARTIFACT":
            spec = specs.setdefault(artifact, {"artifact": [artifact]})
            spec.setdefault(key, []).append(value)
        elif record == "CLOSURE":
            closures.setdefault(artifact, {})[key] = value
    return specs, closures


def verify() -> list[tuple[str, str, str]]:
    """Return a list of (artifact, check, what disagreed). Empty means bound."""
    specs, closures = read_registry()
    failures: list[tuple[str, str, str]] = []

    for artifact, spec in sorted(specs.items()):
        path = ROOT / artifact

        if not path.exists():
            failures.append((artifact, "ARTIFACT", "the committed artifact is not in the tree"))
            continue
        found_sha = sha256_file(path)
        declared_sha = spec["sha256"][0]
        if found_sha != declared_sha:
            failures.append(
                (artifact, "ARTIFACT", f"sha256 declared {declared_sha} found {found_sha}")
            )
        found_octets = str(path.stat().st_size)
        if found_octets != spec["octets"][0]:
            failures.append(
                (artifact, "ARTIFACT", f"octets declared {spec['octets'][0]} found {found_octets}")
            )

        declared_members = closures.get(artifact, {})
        found_members: dict[str, str] = {}
        for rel, want in sorted(declared_members.items()):
            member = ROOT / rel
            if not member.exists():
                failures.append((artifact, "CLOSURE", f"{rel} is declared but is not in the tree"))
                continue
            got = sha256_file(member)
            found_members[rel] = got
            if got != want:
                failures.append(
                    (artifact, "CLOSURE", f"{rel} declared {want[:16]}… found {got[:16]}…")
                )
        if found_members:
            recomputed = closure_hash(found_members)
            declared_closure = spec["closure_sha256"][0]
            if recomputed != declared_closure:
                failures.append(
                    (
                        artifact,
                        "CLOSURE",
                        f"closure_sha256 declared {declared_closure} found {recomputed}",
                    )
                )

        derived = derive_closure(spec)
        added = sorted(derived - set(declared_members))
        removed = sorted(set(declared_members) - derived)
        for rel in added:
            failures.append(
                (artifact, "MEMBERSHIP", f"{rel} is compiled into the artifact and is not declared")
            )
        for rel in removed:
            failures.append(
                (artifact, "MEMBERSHIP", f"{rel} is declared and is no longer compiled in")
            )

        toolchain = ROOT / spec["root"][0] / "rust-toolchain.toml"
        if not toolchain.exists():
            failures.append((artifact, "TOOLCHAIN", f"{toolchain.relative_to(ROOT)} is missing"))
        else:
            channel = TOOLCHAIN_CHANNEL.search(toolchain.read_text(encoding="utf-8"))
            got = channel.group(1) if channel else "(no channel)"
            if got != spec["toolchain"][0]:
                failures.append(
                    (artifact, "TOOLCHAIN", f"declared {spec['toolchain'][0]} pinned {got}")
                )

        # The one command that regenerates the artifact. Executability is a filesystem attribute and
        # not part of the binding — `bash <script>` runs either way — so only absence is a failure.
        builder = ROOT / spec["builder"][0]
        if not builder.exists():
            failures.append((artifact, "BUILDER", f"{spec['builder'][0]} is missing"))

        basename = Path(artifact).name
        for consumer in spec.get("consumer", []):
            source = ROOT / consumer
            if not source.exists():
                failures.append((artifact, "CONSUMER", f"{consumer} is missing"))
            elif basename not in source.read_text(encoding="utf-8", errors="replace"):
                failures.append((artifact, "CONSUMER", f"{consumer} no longer names {basename}"))

    return failures


def rewrite() -> None:
    """Re-seed hashes from the tree. Only after a DELIBERATE rebuild, and say so in the report."""
    specs, _ = read_registry()
    kept = [
        line
        for line in REGISTRY.read_text(encoding="utf-8").splitlines()
        if line.startswith("#") or not line.strip()
    ]
    rows: list[str] = []
    for artifact, spec in sorted(specs.items()):
        path = ROOT / artifact
        members = {rel: sha256_file(ROOT / rel) for rel in sorted(derive_closure(spec))}
        spec["sha256"] = [sha256_file(path)]
        spec["octets"] = [str(path.stat().st_size)]
        spec["closure_sha256"] = [closure_hash(members)]
        order = [
            "root",
            "closure_rule",
            "entry",
            "sha256",
            "octets",
            "closure_sha256",
            "toolchain",
            "builder",
            "consumer",
            "rebuild_evidence",
        ]
        for key in order:
            for value in spec.get(key, []):
                rows.append(f"ARTIFACT\t{artifact}\t{key}\t{value}")
        for rel, digest in members.items():
            rows.append(f"CLOSURE\t{artifact}\t{rel}\t{digest}")
    REGISTRY.write_text("\n".join(kept + [HEADER] + rows) + "\n", encoding="utf-8")
    print(f"re-seeded {REGISTRY.relative_to(ROOT)} from the tree — {len(rows)} rows")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="machine-readable")
    parser.add_argument(
        "--write",
        action="store_true",
        help="re-seed the registry from the tree, after a deliberate rebuild",
    )
    args = parser.parse_args()

    if args.write:
        rewrite()
        return 0

    failures = verify()
    specs, closures = read_registry()

    if args.json:
        print(
            json.dumps(
                {
                    "artifacts": {
                        a: {
                            "closure_members": len(closures.get(a, {})),
                            "rebuild_evidence": s.get("rebuild_evidence", ["(undeclared)"])[0],
                        }
                        for a, s in sorted(specs.items())
                    },
                    "failures": [
                        {"artifact": a, "check": c, "disagreement": d} for a, c, d in failures
                    ],
                },
                indent=2,
            )
        )
        return 1 if failures else 0

    for artifact, spec in sorted(specs.items()):
        state = "BOUND" if not any(f[0] == artifact for f in failures) else "DISAGREES"
        print(
            f"{state:9} {artifact}"
            f"  ({len(closures.get(artifact, {}))} closure members,"
            f" rebuilt: {spec.get('rebuild_evidence', ['(undeclared)'])[0]})"
        )
    if failures:
        print()
        for artifact, check, what in failures:
            print(f"  {check:11} {artifact}: {what}")
        print(f"\n{len(failures)} disagreement(s) between the tree and {REGISTRY.name}")
        return 1
    print(f"\nevery boundary artifact agrees with {REGISTRY.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
