"""Owner-only CLI for a blind side-by-side Athena receipt.

This is an exterior receiver over two response faces. It performs no HNN work and
is not an evaluation partition reader. The input and seed are supplied by the
caller as owner-only files; only the package is shown to the judge before marks
are complete.

Commands:
  prepare --input INPUT.json --seed-file SEED --package CASES.json
  mark --package CASES.json --marks MARKS.json --coordinate ID \
       --left {answers,justified-refusal,fails} \
       --right {answers,justified-refusal,fails} --better {left,right,tie}
  unblind --input INPUT.json --seed-file SEED --package CASES.json \
       --marks MARKS.json --key KEY.json

Output on stdout is limited to counts and hashes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
import tempfile
from pathlib import Path
from typing import Any


INPUT_SCHEMA = "holonics.athena-blind-input.v1"
PACKAGE_SCHEMA = "holonics.athena-blind-package.v1"
MARKS_SCHEMA = "holonics.athena-blind-marks.v1"
KEY_SCHEMA = "holonics.athena-blind-key.v1"
SEED_DOMAIN = b"holonics/athena-blind/seed-commitment/v1\0"
ORDER_DOMAIN = b"holonics/athena-blind/side-order/v1\0"
DISPOSITIONS = ("answers", "justified-refusal", "fails")
BETTER = ("left", "right", "tie")


class BlindError(Exception):
    """A safe-to-report input, state, or permission error."""


def _canonical(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8") + b"\n"


def _object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BlindError("duplicate JSON field")
        result[key] = value
    return result


def _parse_json(raw: bytes) -> Any:
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=_object_pairs,
                          parse_constant=lambda _value: (_ for _ in ()).throw(
                              BlindError("non-finite JSON number")))
    except BlindError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise BlindError("invalid UTF-8 JSON") from exc


def _secure_input(path: Path) -> bytes:
    if path.is_symlink():
        raise BlindError("input path may not be a symlink")
    try:
        info = path.stat()
    except OSError as exc:
        raise BlindError("input file unavailable") from exc
    if not stat.S_ISREG(info.st_mode):
        raise BlindError("input must be a regular file")
    if hasattr(os, "getuid") and info.st_uid != os.getuid():
        raise BlindError("input must be owned by the current user")
    if stat.S_IMODE(info.st_mode) & 0o077:
        raise BlindError("input file must be owner-only")
    try:
        return path.read_bytes()
    except OSError as exc:
        raise BlindError("input file unavailable") from exc


def _secure_directory(path: Path) -> None:
    try:
        path.mkdir(mode=0o700, parents=True, exist_ok=True)
        info = path.stat()
    except OSError as exc:
        raise BlindError("private directory unavailable") from exc
    if not stat.S_ISDIR(info.st_mode) or path.is_symlink():
        raise BlindError("private directory must be a real directory")
    if hasattr(os, "getuid") and info.st_uid != os.getuid():
        raise BlindError("private directory must be owned by the current user")
    os.chmod(path, 0o700)


def _check_private_file(path: Path, *, must_exist: bool = False) -> None:
    if path.is_symlink():
        raise BlindError("private file path may not be a symlink")
    if must_exist:
        try:
            info = path.stat()
        except OSError as exc:
            raise BlindError("private file unavailable") from exc
        if not stat.S_ISREG(info.st_mode):
            raise BlindError("private path must be a regular file")
        if hasattr(os, "getuid") and info.st_uid != os.getuid():
            raise BlindError("private file must be owned by the current user")
        if stat.S_IMODE(info.st_mode) & 0o077:
            raise BlindError("private file must be owner-only")


def _atomic_private_write(path: Path, raw: bytes, *, replace: bool) -> None:
    _secure_directory(path.parent)
    _check_private_file(path)
    if path.exists() and not replace:
        raise BlindError("destination already exists")
    fd, temp_name = tempfile.mkstemp(prefix=".athena-blind-", dir=path.parent)
    try:
        os.fchmod(fd, 0o600)
        with os.fdopen(fd, "wb") as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        if not replace and path.exists():
            raise BlindError("destination already exists")
        os.replace(temp_name, path)
        os.chmod(path, 0o600)
        dir_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def _read_private_json(path: Path) -> tuple[Any, bytes]:
    raw = _secure_input(path)
    return _parse_json(raw), raw


def _read_seed(path: Path) -> bytes:
    seed = _secure_input(path)
    seed = seed.rstrip(b"\r\n")
    if not seed or b"\0" in seed:
        raise BlindError("seed file must contain nonempty bytes without NUL")
    return seed


def _expect_fields(value: Any, fields: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != fields:
        raise BlindError(f"invalid {where} fields")
    return value


def _source_cases(document: Any) -> tuple[list[str], dict[str, dict[str, Any]]]:
    root = _expect_fields(document, {"schema", "coordinate_order", "cases"}, "input")
    if root["schema"] != INPUT_SCHEMA:
        raise BlindError("unsupported input schema")
    order = root["coordinate_order"]
    cases = root["cases"]
    if not isinstance(order, list) or not order or not all(
            isinstance(item, str) and item for item in order):
        raise BlindError("coordinate_order must be a nonempty string list")
    if len(set(order)) != len(order):
        raise BlindError("coordinate_order contains duplicates")
    if not isinstance(cases, list) or len(cases) != len(order):
        raise BlindError("cases must match coordinate_order")
    indexed: dict[str, dict[str, Any]] = {}
    for item in cases:
        case = _expect_fields(item, {"coordinate", "request", "context", "grain", "responses"}, "case")
        coordinate = case["coordinate"]
        if not isinstance(coordinate, str) or not coordinate or coordinate in indexed:
            raise BlindError("case coordinate must be unique and nonempty")
        if not all(isinstance(case[name], str) for name in ("request", "context", "grain")):
            raise BlindError("request, context, and declared grain must be text")
        responses = _expect_fields(case["responses"], {"athena", "control"}, "responses")
        for source in ("athena", "control"):
            response = _expect_fields(responses[source], {"label", "text"}, "response")
            if not isinstance(response["label"], str) or not response["label"]:
                raise BlindError("source labels must be nonempty text")
            if not isinstance(response["text"], str):
                raise BlindError("response text must be text")
        indexed[coordinate] = case
    if set(indexed) != set(order):
        raise BlindError("coordinate_order must name each case exactly once")
    return order, indexed


def _seed_commitment(seed: bytes) -> str:
    return hashlib.sha256(SEED_DOMAIN + seed).hexdigest()


def _athena_left(seed: bytes, coordinate: str) -> bool:
    digest = hashlib.sha256(ORDER_DOMAIN + seed + b"\0" + coordinate.encode("utf-8")).digest()
    return bool(digest[0] & 1)


def _make_package(document: Any, input_raw: bytes, seed: bytes) -> dict[str, Any]:
    order, cases = _source_cases(document)
    visible = []
    for index, coordinate in enumerate(order):
        case = cases[coordinate]
        athena_left = _athena_left(seed, coordinate)
        left = case["responses"]["athena" if athena_left else "control"]["text"]
        right = case["responses"]["control" if athena_left else "athena"]["text"]
        visible.append({"coordinate": coordinate, "order_index": index,
                        "request": case["request"], "context": case["context"],
                        "grain": case["grain"],
                        "left": left, "right": right})
    return {"schema": PACKAGE_SCHEMA, "seed_commitment": _seed_commitment(seed),
            "input_sha256": hashlib.sha256(input_raw).hexdigest(), "cases": visible}


def prepare(input_path: Path, seed_path: Path, package_path: Path) -> dict[str, Any]:
    document, input_raw = _read_private_json(input_path)
    seed = _read_seed(seed_path)
    package = _make_package(document, input_raw, seed)
    package_raw = _canonical(package)
    _atomic_private_write(package_path, package_raw, replace=False)
    return {"cases": len(package["cases"]), "package_sha256": hashlib.sha256(package_raw).hexdigest()}


def _load_package(path: Path) -> tuple[dict[str, Any], bytes]:
    package, raw = _read_private_json(path)
    root = _expect_fields(package, {"schema", "seed_commitment", "input_sha256", "cases"}, "package")
    if root["schema"] != PACKAGE_SCHEMA or not isinstance(root["cases"], list) or not root["cases"]:
        raise BlindError("invalid blind package")
    coordinates = []
    for index, item in enumerate(root["cases"]):
        case = _expect_fields(item, {"coordinate", "order_index", "request", "context", "grain", "left", "right"}, "package case")
        if (type(case["order_index"]) is not int or case["order_index"] != index
                or not isinstance(case["coordinate"], str)):
            raise BlindError("package order is invalid")
        if not all(isinstance(case[k], str) for k in ("request", "context", "grain", "left", "right")):
            raise BlindError("package faces must be text")
        coordinates.append(case["coordinate"])
    if len(coordinates) != len(set(coordinates)):
        raise BlindError("package coordinates are duplicated")
    if not isinstance(root["seed_commitment"], str) or len(root["seed_commitment"]) != 64:
        raise BlindError("package seed commitment is invalid")
    if not isinstance(root["input_sha256"], str) or len(root["input_sha256"]) != 64:
        raise BlindError("package input digest is invalid")
    return root, raw


def _load_marks(path: Path, package_digest: str) -> dict[str, Any]:
    _check_private_file(path, must_exist=path.exists())
    if not path.exists():
        return {"schema": MARKS_SCHEMA, "package_sha256": package_digest, "marks": []}
    marks, _raw = _read_private_json(path)
    root = _expect_fields(marks, {"schema", "package_sha256", "marks"}, "marks")
    if root["schema"] != MARKS_SCHEMA or root["package_sha256"] != package_digest or not isinstance(root["marks"], list):
        raise BlindError("marks do not belong to this package")
    seen: set[str] = set()
    for item in root["marks"]:
        mark = _expect_fields(item, {"coordinate", "left", "right", "better"}, "mark")
        if (not isinstance(mark["coordinate"], str) or mark["coordinate"] in seen
                or mark["left"] not in DISPOSITIONS or mark["right"] not in DISPOSITIONS
                or mark["better"] not in BETTER):
            raise BlindError("marks contain an invalid or repeated mark")
        seen.add(mark["coordinate"])
    return root


def mark(package_path: Path, marks_path: Path, coordinate: str,
         left: str, right: str, better: str) -> dict[str, Any]:
    package, package_raw = _load_package(package_path)
    digest = hashlib.sha256(package_raw).hexdigest()
    coords = [case["coordinate"] for case in package["cases"]]
    if coordinate not in coords:
        raise BlindError("coordinate is not in this package")
    if left not in DISPOSITIONS or right not in DISPOSITIONS or better not in BETTER:
        raise BlindError("mark value is outside the frozen rubric")
    current = _load_marks(marks_path, digest)
    existing = {item["coordinate"] for item in current["marks"]}
    if coordinate in existing:
        raise BlindError("coordinate already has a committed mark")
    current["marks"].append({"coordinate": coordinate, "left": left,
                             "right": right, "better": better})
    # Keep the mark file in pinned coordinate order, independent of entry time.
    rank = {value: index for index, value in enumerate(coords)}
    current["marks"].sort(key=lambda item: rank[item["coordinate"]])
    _atomic_private_write(marks_path, _canonical(current), replace=marks_path.exists())
    return {"marked": len(current["marks"]), "total": len(coords),
            "marks_sha256": hashlib.sha256(_canonical(current)).hexdigest()}


def unblind(input_path: Path, seed_path: Path, package_path: Path,
            marks_path: Path, key_path: Path) -> dict[str, Any]:
    package, package_raw = _load_package(package_path)
    package_digest = hashlib.sha256(package_raw).hexdigest()
    current = _load_marks(marks_path, package_digest)
    coords = [case["coordinate"] for case in package["cases"]]
    if [item["coordinate"] for item in current["marks"]] != coords:
        raise BlindError("all case marks must be committed before unblinding")
    document, input_raw = _read_private_json(input_path)
    seed = _read_seed(seed_path)
    if _seed_commitment(seed) != package["seed_commitment"]:
        raise BlindError("seed does not match the package commitment")
    if hashlib.sha256(input_raw).hexdigest() != package["input_sha256"]:
        raise BlindError("source input does not match the package")
    expected = _make_package(document, input_raw, seed)
    if _canonical(expected) != package_raw:
        raise BlindError("package does not match the supplied source and seed")
    _check_private_file(key_path)
    if key_path.exists():
        raise BlindError("unblinding key already exists")
    _order, cases = _source_cases(document)
    mapping = []
    for coordinate in coords:
        athena_left = _athena_left(seed, coordinate)
        mapping.append({"coordinate": coordinate,
                        "left_source": cases[coordinate]["responses"]["athena" if athena_left else "control"]["label"],
                        "right_source": cases[coordinate]["responses"]["control" if athena_left else "athena"]["label"]})
    key = {"schema": KEY_SCHEMA, "package_sha256": package_digest,
           "marks_sha256": hashlib.sha256(_canonical(current)).hexdigest(),
           "seed_commitment": package["seed_commitment"], "sources": mapping}
    key_raw = _canonical(key)
    _atomic_private_write(key_path, key_raw, replace=False)
    return {"unblinded": len(mapping), "key_sha256": hashlib.sha256(key_raw).hexdigest()}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    p = commands.add_parser("prepare")
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--seed-file", type=Path, required=True)
    p.add_argument("--package", type=Path, required=True)
    m = commands.add_parser("mark")
    m.add_argument("--package", type=Path, required=True)
    m.add_argument("--marks", type=Path, required=True)
    m.add_argument("--coordinate", required=True)
    m.add_argument("--left", choices=DISPOSITIONS, required=True)
    m.add_argument("--right", choices=DISPOSITIONS, required=True)
    m.add_argument("--better", choices=BETTER, required=True)
    u = commands.add_parser("unblind")
    u.add_argument("--input", type=Path, required=True)
    u.add_argument("--seed-file", type=Path, required=True)
    u.add_argument("--package", type=Path, required=True)
    u.add_argument("--marks", type=Path, required=True)
    u.add_argument("--key", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "prepare":
            receipt = prepare(args.input, args.seed_file, args.package)
        elif args.command == "mark":
            receipt = mark(args.package, args.marks, args.coordinate,
                           args.left, args.right, args.better)
        else:
            receipt = unblind(args.input, args.seed_file, args.package, args.marks, args.key)
    except BlindError as exc:
        print(f"refused: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
