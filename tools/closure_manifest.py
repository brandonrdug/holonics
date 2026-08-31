#!/usr/bin/env python3
"""Bind every return under `output/` to the CLOSURE that produced it, not only to its content.

`CLAUDE.md` §0 lesson 1, whole: *"Bind every deposit to its content hash **AND its closure hash**,
with a verifier."* `tools/output_manifest.py` is the content half and says so in its own header —
*"The closure half still has no owner."* This is that owner.

    python3 tools/closure_manifest.py            # rewrite meta/CLOSURE_MANIFEST.tsv
    python3 tools/closure_manifest.py --check    # exit 1 if the tree disagrees with the manifest
    python3 tools/closure_manifest.py --orphans  # print returns whose producer is not in the tree
    python3 tools/closure_manifest.py --self-test # synthetic closure and orphan controls

# What a closure hash is, and why the content hash cannot do its job

A content hash answers *"is this artifact the bytes it was?"*. It cannot answer *"was this artifact
produced by the code it claims to have been produced by?"* — and that is the question the two lost
probe binaries make concrete. `zz_smith_cost_probe` and `zz_torsion_width_law` ran from `target/`,
returned real cost laws, and **their sources were never committed**. Their content hashes would have
verified perfectly right up until the binaries were deleted, because a content hash of a return says
nothing about the producer of that return.

So the repository-local closure of a return is:

    the Cargo example target source
      + the root workspace manifest, lockfile, toolchain, and Cargo configuration
      + every transitive repository-local path package
      + each package manifest, build script, compiled Rust source, and literal include/path module
      + every CUDA/kernel/include source owned by those packages

hashed together. If any of those move, the closure hash moves, and a return whose closure hash no
longer matches is **a return the current tree cannot reproduce** — which is exactly the condition
that lost the tiger figures and the residue-stratum atlas.

# The orphan is the finding, not the error

A return under `output/` whose producing Cargo target is **not in the tree at all** is an orphan:
evidence with no reproducible source. `--orphans` lists it. An orphan may remain only as
`historical` testimony with an existing evidence reference in `meta/ORPHAN_DISPOSITIONS.tsv`.
A `live` or undispositioned orphan fails and manifest regeneration refuses it. **The two `zz_`
probes are historical orphans by construction — their returns are gone too, so they appear nowhere,
and that is the shape of the loss: it leaves no current output root to find.**

# No aperture

Every driver directory under `output/` is bound, uniformly. The producing driver is located by its
file stem (with `-` read as `_`) or by a literal `DEFAULT_OUT = "output/<slug>/…"` in that driver.
Two drivers declaring one address refuse. A directory whose driver cannot be located is reported
rather than skipped silently.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "output"
MANIFEST = ROOT / "meta" / "CLOSURE_MANIFEST.tsv"
ORPHAN_DISPOSITIONS = ROOT / "meta" / "ORPHAN_DISPOSITIONS.tsv"
METADATA_TIMEOUT_SECONDS = 175

HEADER = (
    "# Closure addresses of the returns under `output/`.\n"
    "# One row per driver. `closure` covers the Cargo target, root workspace/lock/toolchain/config,\n"
    "# every transitive local path package, package manifests/build scripts, Rust sources, explicit\n"
    "# include/path-module inputs, and CUDA/kernel/include sources.\n"
    "# `producer` is `ORPHAN` when no driver in the tree bears the directory's name: that is a\n"
    "# return the tree cannot reproduce, and it is reported rather than skipped.\n"
    "driver\tproducer\tclosure\tsources\n"
)

# Explicit path modules are compiled into the declaring driver/helper even when they live outside
# the crate's ordinary `src/` tree.  Resolve them relative to the declaring file, as rustc does
# for a non-inline `mod`, and walk their own path modules transitively.  This does not scan sibling
# examples or infer ordinary `mod foo;` resolution: the crate closure owns the latter.
PATH_MODULE = re.compile(
    r"#\[\s*path\s*=\s*\"([^\"]+)\"\s*\]\s*"
    r"mod\s+[A-Za-z_][A-Za-z0-9_]*\s*;",
    re.MULTILINE,
)

# A driver may name a returned deed rather than itself. A literal DEFAULT_OUT keeps that exterior
# address in the producing source, where closure_of can bind it without an authored alias table.
# Both a directory family at output/<one slug> and a single member below that directory are
# admitted; computed paths remain unresolved and therefore ORPHAN.
DEFAULT_OUTPUT_SLUG = re.compile(
    r'^\s*(?:pub\s+)?const\s+DEFAULT_OUT\s*:\s*&str\s*=\s*"output/([^"/]+)(?:/[^"/]+)?"\s*;',
    re.MULTILINE,
)

INCLUDE_REFERENCE = re.compile(
    r'\b(?:include|include_str|include_bytes)!\s*\(\s*"([^"]+)"\s*\)',
    re.MULTILINE,
)

SOURCE_SUFFIXES = {
    ".rs",
    ".c",
    ".cc",
    ".cpp",
    ".cuh",
    ".cu",
    ".h",
    ".hpp",
    ".s",
    ".S",
    ".ptx",
}


@dataclass(frozen=True)
class CargoExampleTarget:
    name: str
    source: Path
    package_id: str
    package_root: Path


@dataclass(frozen=True)
class CargoGraph:
    root: Path
    payload: dict[str, object]
    packages: dict[str, dict[str, object]]
    local_package_ids: frozenset[str]
    dependencies: dict[str, tuple[str, ...]]
    examples: tuple[CargoExampleTarget, ...]


def cargo_metadata(root: Path) -> dict[str, object]:
    """Return Cargo's resolved graph without compiling a target."""

    try:
        completed = subprocess.run(
            ["cargo", "metadata", "--format-version", "1", "--locked"],
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


def cargo_graph(root: Path = ROOT) -> CargoGraph:
    """Resolve example targets and transitive repository-local package dependencies."""

    root = root.resolve()
    payload = cargo_metadata(root)
    packages = {
        str(package["id"]): package
        for package in payload.get("packages", [])
        if isinstance(package, dict)
    }
    local: set[str] = set()
    for package_id, package in packages.items():
        manifest = Path(str(package["manifest_path"])).resolve()
        source = package.get("source")
        try:
            manifest.relative_to(root)
        except ValueError:
            if source is None:
                raise RuntimeError(
                    f"unreproducible local path dependency outside repository: {manifest}"
                )
            continue
        local.add(package_id)

    dependency_map: dict[str, tuple[str, ...]] = {}
    resolve = payload.get("resolve")
    nodes = resolve.get("nodes", []) if isinstance(resolve, dict) else []
    for node in nodes:
        if not isinstance(node, dict):
            continue
        package_id = str(node["id"])
        deps = tuple(
            sorted(
                str(dependency["pkg"])
                for dependency in node.get("deps", [])
                if isinstance(dependency, dict)
                and str(dependency.get("pkg")) in local
            )
        )
        dependency_map[package_id] = deps

    examples: list[CargoExampleTarget] = []
    for package_id in sorted(local):
        package = packages[package_id]
        manifest = Path(str(package["manifest_path"])).resolve()
        for target in package.get("targets", []):
            if not isinstance(target, dict) or "example" not in target.get("kind", []):
                continue
            source = Path(str(target["src_path"])).resolve()
            if not source.is_file():
                raise RuntimeError(
                    f"Cargo example target {target.get('name')!r} has no source at {source}"
                )
            examples.append(
                CargoExampleTarget(
                    name=str(target["name"]),
                    source=source,
                    package_id=package_id,
                    package_root=manifest.parent,
                )
            )
    examples.sort(key=lambda target: (str(target.source), target.name))
    return CargoGraph(
        root=root,
        payload=payload,
        packages=packages,
        local_package_ids=frozenset(local),
        dependencies=dependency_map,
        examples=tuple(examples),
    )


def driver_sources(graph: CargoGraph) -> dict[str, CargoExampleTarget]:
    """Every Cargo example target, keyed by target/stem and declared output address."""

    found: dict[str, CargoExampleTarget] = {}

    def bind(address: str, target: CargoExampleTarget) -> None:
        prior = found.get(address)
        if prior is not None and prior != target:
            raise RuntimeError(
                f"return address {address!r} is declared by both "
                f"{prior.source.relative_to(graph.root)} and "
                f"{target.source.relative_to(graph.root)}"
            )
        found[address] = target

    for target in graph.examples:
        bind(target.name, target)
        bind(target.source.stem, target)
    for target in graph.examples:
        text = target.source.read_text(encoding="utf-8", errors="replace")
        for match in DEFAULT_OUTPUT_SLUG.finditer(text):
            bind(match.group(1), target)
    return found


@lru_cache(maxsize=None)
def file_digest(source: Path) -> str:
    """Hash a source occurrence once per manifest reading."""

    return hashlib.sha256(source.read_bytes()).hexdigest()


def workspace_members(root: Path) -> tuple[Path, ...]:
    """Workspace resolution inputs shared by every Cargo target."""

    candidates = [
        root / "Cargo.toml",
        root / "Cargo.lock",
        root / "rust-toolchain",
        root / "rust-toolchain.toml",
        root / ".cargo" / "config",
        root / ".cargo" / "config.toml",
    ]
    return tuple(path for path in candidates if path.is_file())


def package_members(graph: CargoGraph, package_id: str) -> tuple[Path, ...]:
    """Source/configuration inputs owned by one repository-local Cargo package."""

    package = graph.packages[package_id]
    manifest = Path(str(package["manifest_path"])).resolve()
    package_root = manifest.parent
    members: set[Path] = {manifest}
    for candidate in (
        package_root / "build.rs",
        package_root / "rust-toolchain",
        package_root / "rust-toolchain.toml",
        package_root / ".cargo" / "config",
        package_root / ".cargo" / "config.toml",
    ):
        if candidate.is_file():
            members.add(candidate)

    source_root = package_root / "src"
    if source_root.is_dir():
        members.update(path for path in source_root.rglob("*.rs") if path.is_file())
    for directory in ("kernels", "kernel", "include"):
        base = package_root / directory
        if not base.is_dir():
            continue
        members.update(
            path
            for path in base.rglob("*")
            if path.is_file() and path.suffix in SOURCE_SUFFIXES
        )

    # Cargo may place a library, binary, or build target outside `src/`. Examples are handled by
    # their individual target source and are not all pulled into every sibling example closure.
    for target in package.get("targets", []):
        if not isinstance(target, dict):
            continue
        kinds = set(target.get("kind", []))
        if kinds.intersection({"lib", "rlib", "proc-macro", "bin", "custom-build"}):
            source = Path(str(target["src_path"])).resolve()
            if source.is_file():
                members.add(source)
    return tuple(sorted(members))


def path_module_references(text: str) -> tuple[str, ...]:
    """Return declared `#[path]` targets in source order for a pure parser exercise."""

    return tuple(match.group(1) for match in PATH_MODULE.finditer(text))


def literal_source_inputs(source: Path, root: Path = ROOT) -> tuple[Path, ...]:
    """Return transitive literal ``#[path]`` and ``include*!`` inputs for ``source``.

    The walk is cycle-safe and deterministic. Missing targets and paths outside this repository
    are not source occurrences and therefore do not enter this manifest's closure.
    """

    entry = source.resolve()
    seen: set[Path] = set()
    discovered: set[Path] = set()
    pending = [entry]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        if not current.is_file():
            continue
        try:
            current.relative_to(root)
        except ValueError:
            continue
        text = current.read_text(encoding="utf-8", errors="replace")
        references = [*path_module_references(text)]
        references.extend(match.group(1) for match in INCLUDE_REFERENCE.finditer(text))
        for relative in references:
            target = (current.parent / relative).resolve()
            if not target.is_file():
                continue
            try:
                target.relative_to(root)
            except ValueError:
                continue
            if target not in discovered:
                discovered.add(target)
                pending.append(target)
    discovered.discard(entry)
    return tuple(sorted(discovered))


def transitive_local_packages(graph: CargoGraph, package_id: str) -> tuple[str, ...]:
    """Return the complete repository-local dependency population for one package."""

    seen: set[str] = set()
    pending = [package_id]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        if current not in graph.local_package_ids:
            continue
        seen.add(current)
        pending.extend(graph.dependencies.get(current, ()))
    return tuple(sorted(seen))


def closure_members(graph: CargoGraph, target: CargoExampleTarget) -> tuple[Path, ...]:
    members: set[Path] = set(workspace_members(graph.root))
    members.add(target.source)
    members.update(literal_source_inputs(target.source, graph.root))
    for package_id in transitive_local_packages(graph, target.package_id):
        for member in package_members(graph, package_id):
            members.add(member)
            if member.suffix == ".rs":
                members.update(literal_source_inputs(member, graph.root))
    return tuple(sorted(member for member in members if member.is_file()))


def closure_of(graph: CargoGraph, target: CargoExampleTarget) -> tuple[str, int]:
    """Hash the Cargo target's complete repository-local source/configuration closure."""

    members = closure_members(graph, target)
    digest = hashlib.sha256()
    counted = 0
    for member in members:
        if not member.is_file():
            continue
        digest.update(str(member.relative_to(graph.root)).encode())
        digest.update(b"\0")
        digest.update(file_digest(member).encode())
        digest.update(b"\n")
        counted += 1
    return digest.hexdigest(), counted


def orphan_dispositions(path: Path = ORPHAN_DISPOSITIONS) -> dict[str, tuple[str, str, str]]:
    """Read ``driver -> (disposition, evidence, note)`` from the explicit ledger."""

    if not path.is_file():
        raise RuntimeError(f"missing orphan disposition ledger {path}")
    returned: dict[str, tuple[str, str, str]] = {}
    for line_at, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if fields == ["driver", "disposition", "evidence", "note"]:
            continue
        if len(fields) != 4:
            raise RuntimeError(
                f"{path}: line {line_at} must have driver/disposition/evidence/note"
            )
        driver, disposition, evidence, note = fields
        if not driver or driver in returned:
            raise RuntimeError(f"{path}: invalid or repeated driver at line {line_at}")
        if disposition not in {"historical", "live"}:
            raise RuntimeError(
                f"{path}: line {line_at} disposition must be historical or live"
            )
        if disposition == "historical" and (not evidence or evidence == "-"):
            raise RuntimeError(
                f"{path}: historical orphan {driver} requires an evidence reference"
            )
        returned[driver] = (disposition, evidence, note)
    return returned


def orphan_disposition_failures(
    built: list[tuple[str, str, str, int]],
    dispositions: dict[str, tuple[str, str, str]],
    root: Path = ROOT,
) -> list[str]:
    """Return missing, live, or unreconstructible historical orphan dispositions."""

    failures: list[str] = []
    root = root.resolve()
    for slug, (kind, evidence, _) in sorted(dispositions.items()):
        if kind == "live":
            failures.append(f"output/{slug}: live ORPHAN has no producer")
            continue
        evidence_path = (root / evidence).resolve()
        try:
            evidence_path.relative_to(root)
        except ValueError:
            failures.append(f"output/{slug}: historical evidence escapes repository: {evidence}")
            continue
        if not evidence_path.is_file():
            failures.append(f"output/{slug}: historical evidence is missing: {evidence}")

    for slug, producer, _, _ in built:
        if producer != "ORPHAN":
            continue
        disposition = dispositions.get(slug)
        if disposition is None:
            failures.append(f"output/{slug}: ORPHAN has no explicit disposition")
    return failures


def rows(
    root: Path = ROOT,
    output: Path = OUTPUT,
    graph: CargoGraph | None = None,
) -> list[tuple[str, str, str, int]]:
    if not output.is_dir():
        return []
    graph = graph or cargo_graph(root)
    drivers = driver_sources(graph)
    built: list[tuple[str, str, str, int]] = []
    for directory in sorted(p for p in output.iterdir() if p.is_dir()):
        slug = directory.name
        candidate = drivers.get(slug) or drivers.get(slug.replace("-", "_"))
        if candidate is None:
            built.append((slug, "ORPHAN", "-", 0))
            continue
        digest, counted = closure_of(graph, candidate)
        built.append((slug, str(candidate.source.relative_to(root)), digest, counted))
    return built


def render(built: list[tuple[str, str, str, int]]) -> str:
    body = "".join(f"{slug}\t{producer}\t{digest}\t{count}\n" for slug, producer, digest, count in built)
    return HEADER + body


def self_test() -> None:
    """Exercise Cargo target discovery, local dependency closure, CUDA, and orphan policy."""

    with tempfile.TemporaryDirectory(prefix="holonics-closure-manifest-") as temporary:
        root = Path(temporary).resolve()
        (root / "app" / "src").mkdir(parents=True)
        (root / "app" / "examples" / "support").mkdir(parents=True)
        (root / "app" / "kernels").mkdir(parents=True)
        (root / "dep" / "src").mkdir(parents=True)
        (root / "research" / "records").mkdir(parents=True)
        (root / "output" / "visible").mkdir(parents=True)
        (root / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["app", "dep"]\nresolver = "2"\n', encoding="utf-8"
        )
        (root / "app" / "Cargo.toml").write_text(
            """[package]
name = "closure-app"
version = "0.0.0"
edition = "2021"
build = "build.rs"

[dependencies]
closure-dep = { path = "../dep" }
""",
            encoding="utf-8",
        )
        (root / "app" / "build.rs").write_text(
            'fn main() { println!("cargo:rerun-if-changed=kernels/law.cu"); }\n',
            encoding="utf-8",
        )
        (root / "app" / "src" / "lib.rs").write_text(
            "pub fn app() -> u8 { closure_dep::dep() }\n", encoding="utf-8"
        )
        (root / "app" / "examples" / "visible.rs").write_text(
            '#[path = "support/helper.rs"]\nmod helper;\nfn main() { helper::run(); }\n',
            encoding="utf-8",
        )
        (root / "app" / "examples" / "support" / "helper.rs").write_text(
            "pub fn run() {}\n", encoding="utf-8"
        )
        (root / "app" / "kernels" / "law.cu").write_text(
            'extern "C" __global__ void law() {}\n', encoding="utf-8"
        )
        (root / "dep" / "Cargo.toml").write_text(
            '[package]\nname = "closure-dep"\nversion = "0.0.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (root / "dep" / "src" / "lib.rs").write_text(
            "pub fn dep() -> u8 { 1 }\n", encoding="utf-8"
        )
        subprocess.run(
            ["cargo", "generate-lockfile"],
            cwd=root,
            check=True,
            capture_output=True,
            text=True,
            timeout=METADATA_TIMEOUT_SECONDS,
        )

        graph = cargo_graph(root)
        assert [target.name for target in graph.examples] == ["visible"]
        target = graph.examples[0]
        members = {str(path.relative_to(root)) for path in closure_members(graph, target)}
        expected = {
            "Cargo.toml",
            "Cargo.lock",
            "app/Cargo.toml",
            "app/build.rs",
            "app/src/lib.rs",
            "app/examples/visible.rs",
            "app/examples/support/helper.rs",
            "app/kernels/law.cu",
            "dep/Cargo.toml",
            "dep/src/lib.rs",
        }
        missing = expected - members
        assert not missing, f"closure omitted {sorted(missing)}"
        baseline_digest, _ = closure_of(graph, target)
        for relative in (
            "Cargo.lock",
            "app/build.rs",
            "app/kernels/law.cu",
            "dep/src/lib.rs",
        ):
            path = root / relative
            standing = path.read_bytes()
            path.write_bytes(standing + b"\n")
            file_digest.cache_clear()
            changed_digest, _ = closure_of(graph, target)
            assert changed_digest != baseline_digest, f"{relative} did not move closure"
            path.write_bytes(standing)
            file_digest.cache_clear()

        (root / "output" / "orphan").mkdir()
        evidence = root / "research" / "records" / "orphan.md"
        evidence.write_text("# historical orphan\n", encoding="utf-8")
        built = rows(root=root, output=root / "output", graph=graph)
        assert any(row[0] == "visible" and row[1] != "ORPHAN" for row in built)
        assert any(row[0] == "orphan" and row[1] == "ORPHAN" for row in built)
        historical = {
            "orphan": ("historical", "research/records/orphan.md", "control")
        }
        assert orphan_disposition_failures(built, historical, root) == []
        assert orphan_disposition_failures(built, {}, root)
        assert orphan_disposition_failures(
            built, {"orphan": ("live", "-", "control")}, root
        )
        assert orphan_disposition_failures(
            built,
            {"orphan": ("historical", "research/records/missing.md", "control")},
            root,
        )
        print(
            "closure-manifest self-test: Cargo target + transitive local package + build/CUDA "
            "closure held; missing/live orphan dispositions refused"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 if the manifest is stale")
    parser.add_argument("--orphans", action="store_true", help="list returns with no producer")
    parser.add_argument(
        "--self-test", action="store_true", help="run synthetic closure and orphan controls"
    )
    arguments = parser.parse_args()

    if arguments.self_test:
        self_test()
        return 0

    try:
        built = rows()
        dispositions = orphan_dispositions()
    except RuntimeError as error:
        print(f"closure-manifest: {error}", file=sys.stderr)
        return 2
    disposition_failures = orphan_disposition_failures(built, dispositions)

    if arguments.orphans:
        orphans = [slug for slug, producer, _, _ in built if producer == "ORPHAN"]
        for slug in orphans:
            disposition = dispositions.get(slug)
            detail = (
                "undispositioned"
                if disposition is None
                else f"{disposition[0]} evidence={disposition[1]}"
            )
            print(f"ORPHAN  output/{slug}  — {detail}")
        for failure in disposition_failures:
            print(f"REFUSED {failure}")
        print(
            f"{len(orphans)} orphan(s) of {len(built)} return directories; "
            f"{len(disposition_failures)} disposition failure(s)"
        )
        return 1 if disposition_failures else 0

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
            for failure in disposition_failures:
                print(f"  orphan: {failure}")
            return 1
        if disposition_failures:
            for failure in disposition_failures:
                print(f"orphan disposition failure: {failure}")
            return 1
        orphans = sum(1 for _, producer, _, _ in built if producer == "ORPHAN")
        print(f"closure manifest current: {len(built)} return directories, {orphans} orphan(s)")
        return 0

    if disposition_failures:
        for failure in disposition_failures:
            print(f"refusing manifest regeneration: {failure}")
        return 1
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(rendered)
    orphans = sum(1 for _, producer, _, _ in built if producer == "ORPHAN")
    print(f"wrote {MANIFEST.relative_to(ROOT)}: {len(built)} return directories, {orphans} orphan(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
