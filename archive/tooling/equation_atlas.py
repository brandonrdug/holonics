#!/usr/bin/env python3
"""Validate the exterior equation atlas as stored material.

This is an exterior repository verifier, not a mathematical adjudicator. It checks the JSON-Schema
subset used by the atlas, manifest content addresses/counts, unique identities, relation endpoints,
and local provenance addresses. It never upgrades a truth grade or consults Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
ATLAS = ROOT / "research" / "equation-atlas"
SCHEMA_PATH = ATLAS / "schema.json"
MANIFEST_PATH = ATLAS / "manifest.json"


def address(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    extent = 0
    with path.open("rb") as source:
        while chunk := source.read(1 << 20):
            digest.update(chunk)
            extent += len(chunk)
    return digest.hexdigest(), extent


def resolve_ref(root: dict[str, Any], reference: str) -> dict[str, Any]:
    if not reference.startswith("#/"):
        raise ValueError(f"unsupported non-local schema reference {reference!r}")
    node: Any = root
    for part in reference[2:].split("/"):
        node = node[part.replace("~1", "/").replace("~0", "~")]
    if not isinstance(node, dict):
        raise ValueError(f"schema reference {reference!r} does not resolve to an object")
    return node


def type_holds(value: Any, kind: str) -> bool:
    return {
        "object": isinstance(value, dict),
        "array": isinstance(value, list),
        "string": isinstance(value, str),
        "integer": isinstance(value, int) and not isinstance(value, bool),
        "number": isinstance(value, (int, float)) and not isinstance(value, bool),
        "boolean": isinstance(value, bool),
        "null": value is None,
    }.get(kind, False)


def validate(value: Any, rule: dict[str, Any], root: dict[str, Any], at: str) -> list[str]:
    if "$ref" in rule:
        return validate(value, resolve_ref(root, rule["$ref"]), root, at)
    if "oneOf" in rule:
        branches = [validate(value, branch, root, at) for branch in rule["oneOf"]]
        passing = sum(not errors for errors in branches)
        if passing == 1:
            return []
        return [f"{at}: expected exactly one schema branch, found {passing}"]
    errors: list[str] = []
    if "const" in rule and value != rule["const"]:
        errors.append(f"{at}: expected constant {rule['const']!r}, found {value!r}")
    if "enum" in rule and value not in rule["enum"]:
        errors.append(f"{at}: {value!r} is outside {rule['enum']!r}")
    kind = rule.get("type")
    if kind is not None and not type_holds(value, kind):
        return [f"{at}: expected {kind}, found {type(value).__name__}"]
    if isinstance(value, str):
        if len(value) < rule.get("minLength", 0):
            errors.append(f"{at}: string is shorter than {rule['minLength']}")
        if "pattern" in rule and re.match(rule["pattern"], value) is None:
            errors.append(f"{at}: {value!r} does not match {rule['pattern']!r}")
    if isinstance(value, list):
        item_rule = rule.get("items")
        if item_rule is not None:
            for index, item in enumerate(value):
                errors.extend(validate(item, item_rule, root, f"{at}[{index}]"))
        if rule.get("uniqueItems"):
            canonical = [json.dumps(item, sort_keys=True, separators=(",", ":")) for item in value]
            if len(canonical) != len(set(canonical)):
                errors.append(f"{at}: array members are not unique")
    if isinstance(value, dict):
        required = set(rule.get("required", []))
        missing = sorted(required - value.keys())
        for name in missing:
            errors.append(f"{at}: missing required field {name!r}")
        properties = rule.get("properties", {})
        if rule.get("additionalProperties") is False:
            for name in sorted(value.keys() - properties.keys()):
                errors.append(f"{at}: unexpected field {name!r}")
        for name, child_rule in properties.items():
            if name in value:
                errors.extend(validate(value[name], child_rule, root, f"{at}.{name}"))
    return errors


def rows(path: Path) -> list[tuple[int, dict[str, Any]]]:
    loaded: list[tuple[int, dict[str, Any]]] = []
    for line_at, line in enumerate(path.read_text().splitlines(), 1):
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"{path.relative_to(ROOT)}:{line_at}: {error}") from error
        if not isinstance(value, dict):
            raise ValueError(f"{path.relative_to(ROOT)}:{line_at}: row is not an object")
        loaded.append((line_at, value))
    return loaded


def local_source_error(reference: str) -> str | None:
    if reference.startswith("external:"):
        return None
    locator = reference.split("#", 1)[0]
    target = ROOT / locator
    if not target.is_file():
        return f"source_ref {reference!r} does not resolve to a regular file"
    return None


def check() -> list[str]:
    failures: list[str] = []
    schema = json.loads(SCHEMA_PATH.read_text())
    manifest = json.loads(MANIFEST_PATH.read_text())
    all_rows: list[tuple[str, int, dict[str, Any]]] = []
    for name in ("equations.jsonl", "relations.jsonl"):
        for line_at, value in rows(ATLAS / name):
            all_rows.append((name, line_at, value))
            failures.extend(
                validate(value, schema, schema, f"research/equation-atlas/{name}:{line_at}")
            )
            source_ref = value.get("source_ref")
            if isinstance(source_ref, str):
                if error := local_source_error(source_ref):
                    failures.append(f"research/equation-atlas/{name}:{line_at}: {error}")

    identities: dict[str, tuple[str, int]] = {}
    equation_ids: set[str] = set()
    for name, line_at, value in all_rows:
        identity = value.get("id")
        if not isinstance(identity, str):
            continue
        if identity in identities:
            prior = identities[identity]
            failures.append(
                f"duplicate id {identity!r}: {prior[0]}:{prior[1]} and {name}:{line_at}"
            )
        identities[identity] = (name, line_at)
        if value.get("record_type") == "equation":
            equation_ids.add(identity)

    for name, line_at, value in all_rows:
        if value.get("record_type") != "relation":
            continue
        if value.get("from") not in equation_ids:
            failures.append(f"{name}:{line_at}: dangling from endpoint {value.get('from')!r}")
        if value.get("to") not in equation_ids:
            failures.append(f"{name}:{line_at}: dangling to endpoint {value.get('to')!r}")
        if value.get("from") == value.get("to"):
            failures.append(f"{name}:{line_at}: relation is a self-edge")

    carried = {item.get("path"): item for item in manifest.get("artifacts", [])}
    for name in ("schema.json", "equations.jsonl", "relations.jsonl"):
        item = carried.get(name)
        if not isinstance(item, dict):
            failures.append(f"manifest has no artifact row for {name}")
            continue
        digest, extent = address(ATLAS / name)
        if item.get("sha256") != digest or item.get("bytes") != extent:
            failures.append(f"manifest address/extent drifted for {name}")
        if name.endswith(".jsonl") and item.get("records") != len(rows(ATLAS / name)):
            failures.append(f"manifest record count drifted for {name}")

    appended = manifest.get("appended_records", [])
    if not isinstance(appended, list) or not all(isinstance(item, str) for item in appended):
        failures.append("manifest appended_records is not a string population")
    else:
        if len(appended) != len(set(appended)):
            failures.append("manifest appended_records contains duplicate addresses")
        for reference in appended:
            if not (ROOT / reference).is_file():
                failures.append(f"manifest appended record {reference!r} does not resolve")
    governing = manifest.get("governing_record")
    if not isinstance(governing, str) or not (ROOT / governing).is_file():
        failures.append("manifest governing_record does not resolve")

    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="retained for gate/tool symmetry")
    parser.parse_args()
    try:
        failures = check()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"equation atlas verifier failed to read its material: {error}")
        return 1
    for failure in failures:
        print(f"FAIL {failure}")
    eq_count = sum(1 for _ in rows(ATLAS / "equations.jsonl"))
    relation_count = sum(1 for _ in rows(ATLAS / "relations.jsonl"))
    print(
        f"equation atlas: {eq_count} equations, {relation_count} relations, "
        f"{len(failures)} failure(s)"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
