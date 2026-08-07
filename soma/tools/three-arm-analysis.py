#!/usr/bin/env python3
"""Deterministic three-arm arithmetic instrument.

Implements the pre-registered base plan plus Amendments I--VII in
``observations/2026-07-11_THE_ANALYSIS_PLAN.md`` and writes the nine artifacts
specified by ``observations/2026-07-11_THREE_ARM_ARTIFACT_SCHEMA.md``.

There is deliberately no exploratory mode, random source, resume path, or
overwrite path.  The only interface is ``--out DIR``.
"""

from __future__ import annotations

import argparse
import contextlib
import csv
import hashlib
import importlib.util
import io
import json
import math
import os
import platform
import shlex
import shutil
import struct
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence

import numpy as np


sys.dont_write_bytecode = True


SCRIPT_PATH = Path(__file__).resolve()
SOMA_ROOT = SCRIPT_PATH.parent.parent
REPO_ROOT = SOMA_ROOT.parent.parent

PLAN_REL = "src/soma/observations/2026-07-11_THE_ANALYSIS_PLAN.md"
SCHEMA_REL = "src/soma/observations/2026-07-11_THREE_ARM_ARTIFACT_SCHEMA.md"
CHEBYSHEV_REL = "src/soma/observations/2026-07-11_prime-seasons-out/chebyshev.csv"
LEGACY_REL = "src/soma/tools/prime-seasons.py"
RUNNER_REL = "src/soma/tools/three-arm-analysis.py"
SOURCE_RELS = tuple(sorted((PLAN_REL, SCHEMA_REL, CHEBYSHEV_REL, LEGACY_REL, RUNNER_REL)))

PLAN_PATH = REPO_ROOT / PLAN_REL
SCHEMA_PATH = REPO_ROOT / SCHEMA_REL
CHEBYSHEV_PATH = REPO_ROOT / CHEBYSHEV_REL
LEGACY_PATH = REPO_ROOT / LEGACY_REL

N_PRIME = 2 ** 28
N_LUCKY = 2 ** 22
WINDOW_WIDTH = np.float64(0.05)
HALF_WINDOW = np.float64(0.025)
U_START = np.float64(math.log(1e4))
MIN_K_EVENTS = 1_000
MIN_S_EVENTS = 1_000
MIN_O_PAIRS = 1_000
MIN_O_PRESENT_WINDOWS = 100

K_TARGETS = (
    np.float64(6.020948904697596),
    np.float64(10.243770304166554),
    np.float64(12.988098012312422),
    np.float64(16.342607104587222),
    np.float64(18.291993196123534),
)
S_ZETA = (
    np.float64(14.134725),
    np.float64(21.022040),
    np.float64(25.010858),
    np.float64(30.424876),
    np.float64(32.935062),
)
ZETA_UNION = (
    np.float64(14.134725),
    np.float64(21.022040),
    np.float64(25.010858),
    np.float64(30.424876),
    np.float64(32.935062),
    np.float64(37.586178),
    np.float64(40.918719),
    np.float64(43.327073),
    np.float64(48.005151),
    np.float64(49.773832),
    np.float64(52.970321),
    np.float64(56.446248),
    np.float64(59.347044),
    np.float64(60.831779),
    np.float64(65.112544),
)
CONTROLS = tuple(np.float64(x) for x in (
    8.0, 9.0, 12.0, 15.5, 19.0, 19.5, 23.0, 27.5, 29.0, 34.5,
    36.0, 39.0, 42.0, 45.0, 47.0, 50.5, 52.0, 55.5, 58.0, 63.0,
))
PSEUDO_COMBS = (
    (np.float64(8.0), np.float64(9.0), np.float64(12.0)),
    (np.float64(15.5), np.float64(19.0), np.float64(19.5)),
    (np.float64(23.0), np.float64(27.5), np.float64(29.0)),
    (np.float64(34.5), np.float64(36.0), np.float64(39.0)),
    (np.float64(42.0), np.float64(45.0), np.float64(47.0)),
)
BETAS = tuple(np.float64(x) for x in (0.40, 0.45, 0.50, 0.55, 0.60))
S_FREQUENCIES = S_ZETA + CONTROLS
SEPARATION_REQUIRED = np.float64(0.6)
EPSILON = np.float64(0.05)

ARTIFACT_NAMES = (
    "k-raw.csv",
    "k-sensitivity.csv",
    "o-classes.csv",
    "o-raw.csv",
    "s-algebra.csv",
    "s-raw.csv",
    "s-sensitivity.csv",
    "table-read.json",
)

K_RAW_HEADER = (
    "record", "material", "window_index", "u_center", "count_1mod4",
    "count_3mod4", "window_lead", "cumulative_lead", "usable", "chi",
    "frequency_role", "frequency", "amplitude", "control_max", "margin",
    "comb_id", "members_above", "comb_pass", "expected_count_1mod4",
    "expected_count_3mod4", "expected_window_lead",
    "expected_cumulative_lead", "comparison_pass",
)
K_SENSITIVITY_HEADER = (
    "material", "target", "frequency_role", "frequency", "base_amplitude",
    "injected_amplitude", "signed_delta", "absolute_delta", "delta_target",
    "delta_control", "positive_margin", "control_margin", "finite", "face_pass",
)
O_RAW_HEADER = (
    "record", "gate", "window_index", "candidate_rank", "a", "b", "retained",
    "real_ab", "real_ba", "surrogate_ab", "surrogate_ba", "real_sign",
    "surrogate_sign", "item_count", "mismatch_count", "first_mismatch_index", "pass",
)
O_CLASSES_HEADER = (
    "whole_rank", "candidate_rank", "a", "b", "whole_orbit_count", "diagonal",
    "present_windows", "retained", "p_real", "m_real", "z_real", "p_surrogate",
    "m_surrogate", "z_surrogate", "lhs_real", "rhs_real", "lhs_surrogate",
    "rhs_surrogate", "departs_real", "departs_surrogate", "orbit_row",
)
S_RAW_HEADER = (
    "record", "face", "beta", "frequency_role", "frequency", "concentration",
    "mass_status", "control_max", "exceedance_margin", "exceeds_control",
    "exceedance_count",
)
S_ALGEBRA_HEADER = (
    "gate", "assertion", "beta", "frequency_role", "frequency", "window_index",
    "compared_count", "left_status", "right_status", "error", "scale", "tolerance",
    "mismatch_count", "first_mismatch_index", "pass",
)
S_SENSITIVITY_HEADER = (
    "frequency_role", "frequency", "base_concentration", "base_status",
    "injected_concentration", "injected_status", "signed_delta", "absolute_delta",
    "delta_target", "delta_control", "positive_margin", "control_margin", "finite",
    "gate_pass",
)

S_WINDOW_COUNT = 204
S_LOG_TWO = np.log(np.float64(2.0))
S_U_LO = U_START - HALF_WINDOW
S_C_203 = U_START + np.float64(203) * WINDOW_WIDTH
S_U_HI = S_C_203 + HALF_WINDOW
S_A_TAU = (S_U_LO + S_U_HI) - np.float64(2.0) * U_START
S_BETAS_ARRAY = np.asarray(BETAS, dtype=np.float64)
S_ZETA_ARRAY = np.asarray(S_ZETA, dtype=np.float64)
S_CONTROLS_ARRAY = np.asarray(CONTROLS, dtype=np.float64)
S_FREQUENCIES_ARRAY = np.concatenate((S_ZETA_ARRAY, S_CONTROLS_ARRAY))
S_K_TARGET_ARRAY = np.asarray(K_TARGETS, dtype=np.float64)
S_ZETA_UNION_ARRAY = np.asarray(ZETA_UNION, dtype=np.float64)
S_UNION_COMB = np.concatenate((S_K_TARGET_ARRAY, S_ZETA_UNION_ARRAY))
MASS = "MASS"
NO_MASS = "NO-MASS"
NOT_EVALUATED = "NOT-EVALUATED"


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--out", required=True, metavar="DIR")
    return parser.parse_args(argv)


def run_git(*args: str) -> str:
    proc = subprocess.run(
        ("git", "-C", str(REPO_ROOT), *args),
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return proc.stdout


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def verify_clean_tracked_sources() -> tuple[str, dict[str, str]]:
    commit = run_git("rev-parse", "HEAD").strip()
    dirty = run_git("status", "--porcelain", "--untracked-files=no")
    if dirty:
        raise RuntimeError("tracked worktree/index is dirty; dispatch refused")

    hashes: dict[str, str] = {}
    for rel in SOURCE_RELS:
        run_git("ls-files", "--error-unmatch", "--", rel)
        subprocess.run(
            ("git", "-C", str(REPO_ROOT), "cat-file", "-e", f"HEAD:{rel}"),
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
        )
        hashes[rel] = sha256_file(REPO_ROOT / rel)
    return commit, hashes


def load_legacy_module() -> Any:
    spec = importlib.util.spec_from_file_location("soma_prime_seasons_committed", LEGACY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load committed source {LEGACY_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def f64_wire(value: Any) -> str:
    value64 = np.float64(value)
    if np.isnan(value64):
        return "nan"
    if np.isposinf(value64):
        return "inf"
    if np.isneginf(value64):
        return "-inf"
    return float(value64).hex()


def csv_cell(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, (bool, np.bool_)):
        return "1" if bool(value) else "0"
    if isinstance(value, (int, np.integer)):
        return str(int(value))
    if isinstance(value, (float, np.floating)):
        return f64_wire(value)
    return str(value)


def json_i(value: Any) -> str:
    return str(int(value))


def json_f(value: Any) -> str:
    return f64_wire(value)


def json_scalar(value: Any) -> Any:
    if value is None:
        return ""
    if isinstance(value, (bool, np.bool_)):
        return bool(value)
    if isinstance(value, (int, np.integer)):
        return json_i(value)
    if isinstance(value, (float, np.floating)):
        return json_f(value)
    return value


def json_inputs(values: dict[str, Any]) -> dict[str, Any]:
    return {key: json_scalar(value) for key, value in values.items()}


def blank_row(header: Sequence[str], **values: Any) -> dict[str, Any]:
    row = {key: None for key in header}
    row.update(values)
    return row


def write_csv(path: Path, header: Sequence[str], rows: Iterable[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(
            handle,
            delimiter=",",
            quotechar='"',
            quoting=csv.QUOTE_MINIMAL,
            lineterminator="\n",
        )
        writer.writerow(header)
        for row in rows:
            writer.writerow([csv_cell(row.get(column)) for column in header])


def write_json(path: Path, value: Any) -> None:
    payload = json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))
    path.write_text(payload + "\n", encoding="utf-8", newline="\n")


def canonical_result_hash(directory: Path) -> str:
    digest = hashlib.sha256()
    for name in sorted(ARTIFACT_NAMES):
        content = (directory / name).read_bytes()
        encoded = name.encode("utf-8")
        digest.update(encoded)
        digest.update(b"\0")
        digest.update(struct.pack("<Q", len(content)))
        digest.update(content)
    return digest.hexdigest()


def numpy_build_config() -> str:
    stream = io.StringIO()
    with contextlib.redirect_stdout(stream):
        np.show_config()
    return stream.getvalue().rstrip("\n")


def sieve_primes(n: int) -> np.ndarray:
    is_prime = np.ones(n + 1, dtype=bool)
    is_prime[0:2] = False
    for candidate in range(2, math.isqrt(n) + 1):
        if is_prime[candidate]:
            is_prime[candidate * candidate::candidate] = False
    return np.flatnonzero(is_prime).astype(np.int64)


def n_windows_for(end: int) -> int:
    return int(math.floor((math.log(end) - float(U_START)) / float(WINDOW_WIDTH))) + 1


def window_centers(count: int) -> np.ndarray:
    return U_START + np.arange(count, dtype=np.float64) * WINDOW_WIDTH


def window_indices(values: np.ndarray) -> np.ndarray:
    u = np.log(values.astype(np.float64))
    return np.floor((u - U_START) / WINDOW_WIDTH + np.float64(0.5)).astype(np.int64)


def separation_face() -> tuple[np.float64, bool]:
    union = K_TARGETS + ZETA_UNION
    distances = [np.float64(abs(control - member)) for control in CONTROLS for member in union]
    minimum = min(distances)
    return minimum, bool(minimum >= SEPARATION_REQUIRED)


@dataclass
class KMaterial:
    name: str
    end: int
    values: np.ndarray
    centers: np.ndarray
    count1: np.ndarray
    count3: np.ndarray
    lead: np.ndarray
    cumulative: np.ndarray
    usable: np.ndarray
    chi: np.ndarray
    amplitudes: list[np.float64 | None]
    control_max: np.float64 | None


@dataclass
class KSensitivityFace:
    material: str
    target: np.float64
    rows: list[dict[str, Any]]
    delta_target: np.float64 | None
    delta_control: np.float64 | None
    positive_margin: np.float64 | None
    control_margin: np.float64 | None
    nonfinite_count: int
    finite: bool
    passed: bool


def build_k_material(name: str, end: int, values: np.ndarray) -> KMaterial:
    count = n_windows_for(end)
    centers = window_centers(count)
    indices = window_indices(values)
    valid = (indices >= 0) & (indices < count)
    residues = values % np.int64(4)
    count1 = np.bincount(indices[valid & (residues == 1)], minlength=count).astype(np.int64)
    count3 = np.bincount(indices[valid & (residues == 3)], minlength=count).astype(np.int64)
    lead = count3 - count1
    cumulative = np.cumsum(lead, dtype=np.int64)
    totals = count1 + count3
    usable = np.flatnonzero(totals >= MIN_K_EVENTS).astype(np.int64)
    if usable.size:
        n1 = count1[usable]
        n3 = count3[usable]
        chi = (n1 - n3).astype(np.float64) / (n1 + n3).astype(np.float64)
    else:
        chi = np.empty(0, dtype=np.float64)
    return KMaterial(
        name=name,
        end=end,
        values=values,
        centers=centers,
        count1=count1,
        count3=count3,
        lead=lead,
        cumulative=cumulative,
        usable=usable,
        chi=chi,
        amplitudes=[],
        control_max=None,
    )


def k_amplitude(series: np.ndarray, centers: np.ndarray, frequency: np.float64) -> np.float64:
    mean = np.sum(series, dtype=np.float64) / np.float64(series.size)
    phase = np.exp((np.complex128(1j) * np.float64(frequency)) * centers)
    total = np.sum(
        (series - mean).astype(np.complex128) * phase,
        dtype=np.complex128,
    )
    return np.float64(np.abs(total))


def populate_k_amplitudes(material: KMaterial) -> None:
    if material.usable.size == 0:
        material.amplitudes = [None] * (len(K_TARGETS) + len(CONTROLS))
        material.control_max = None
        return
    centers = material.centers[material.usable]
    frequencies = K_TARGETS + CONTROLS
    material.amplitudes = [k_amplitude(material.chi, centers, frequency) for frequency in frequencies]
    controls = [value for value in material.amplitudes[len(K_TARGETS):] if value is not None]
    material.control_max = max(controls) if controls else None


def load_chebyshev_expected() -> tuple[dict[int, dict[str, int]], int, int]:
    rows: dict[int, dict[str, int]] = {}
    physical_rows = 0
    duplicate_rows = 0
    with CHEBYSHEV_PATH.open("r", encoding="utf-8", newline="") as handle:
        for source in csv.DictReader(handle):
            physical_rows += 1
            window_index = int(source["window_index"])
            row = {
                "window_index": window_index,
                "count_3mod4": int(source["count_3mod4"]),
                "count_1mod4": int(source["count_1mod4"]),
                "window_lead": int(source["window_lead"]),
                "cumulative_lead": int(source["cumulative_lead"]),
            }
            if window_index in rows:
                duplicate_rows += 1
            else:
                rows[window_index] = row
    return rows, physical_rows, duplicate_rows


def compare_chebyshev(
    real: KMaterial,
    expected: dict[int, dict[str, int]],
    duplicate_rows: int,
) -> tuple[int, list[bool]]:
    comparisons: list[bool] = []
    actual_keys = set(range(len(real.centers)))
    expected_keys = set(expected)
    missing = actual_keys - expected_keys
    extra = expected_keys - actual_keys
    mismatch = duplicate_rows + len(missing) + len(extra)
    for index in range(len(real.centers)):
        if index not in expected:
            comparisons.append(False)
            continue
        row = expected[index]
        passed = (
            row["window_index"] == index
            and row["count_3mod4"] == int(real.count3[index])
            and row["count_1mod4"] == int(real.count1[index])
            and row["window_lead"] == int(real.lead[index])
            and row["cumulative_lead"] == int(real.cumulative[index])
        )
        comparisons.append(passed)
        if not passed:
            mismatch += 1
    return mismatch, comparisons


def amplitude_map(material: KMaterial) -> dict[float, np.float64 | None]:
    frequencies = K_TARGETS + CONTROLS
    return {float(frequency): material.amplitudes[index] for index, frequency in enumerate(frequencies)}


def k_hit(material: KMaterial) -> tuple[int | None, bool | None]:
    if material.control_max is None:
        return None, None
    first = material.amplitudes[:3]
    if any(value is None for value in first):
        return None, None
    above = sum(bool(value > material.control_max) for value in first if value is not None)
    return above, above >= 2


def pseudo_comb_results(real: KMaterial) -> list[tuple[int | None, bool | None]]:
    mapping = amplitude_map(real)
    if real.control_max is None:
        return [(None, None) for _ in PSEUDO_COMBS]
    results: list[tuple[int | None, bool | None]] = []
    for comb in PSEUDO_COMBS:
        members = {float(value) for value in comb}
        outside = [mapping[float(control)] for control in CONTROLS if float(control) not in members]
        if any(value is None for value in outside):
            results.append((None, None))
            continue
        threshold = max(value for value in outside if value is not None)
        count = sum(bool(mapping[float(member)] > threshold) for member in comb)
        results.append((count, count >= 2))
    return results


def build_k_sensitivity_face(material: KMaterial, target: np.float64) -> KSensitivityFace:
    frequencies = (target,) + CONTROLS
    if material.usable.size == 0:
        rows = [blank_row(
            K_SENSITIVITY_HEADER,
            material=material.name,
            target=target,
            frequency_role="TARGET" if index == 0 else "CONTROL",
            frequency=frequency,
        ) for index, frequency in enumerate(frequencies)]
        return KSensitivityFace(material.name, target, rows, None, None, None, None, 0, False, False)

    centers = material.centers[material.usable]
    injected = material.chi + EPSILON * np.cos(np.float64(target) * centers)
    base_values = [k_amplitude(material.chi, centers, frequency) for frequency in frequencies]
    injected_values = [k_amplitude(injected, centers, frequency) for frequency in frequencies]
    signed = [np.float64(after - before) for before, after in zip(base_values, injected_values)]
    absolute = [np.float64(abs(value)) for value in signed]
    delta_target = signed[0]
    delta_control = max(absolute[1:])
    positive_margin = delta_target
    control_margin = np.float64(delta_target - delta_control)
    scalar_quantities = (
        *base_values, *injected_values, *signed, *absolute,
        delta_target, delta_control, positive_margin, control_margin,
    )
    nonfinite_count = sum(not bool(np.isfinite(value)) for value in scalar_quantities)
    finite = nonfinite_count == 0
    passed = bool(finite and delta_target > 0 and delta_target > delta_control)
    rows: list[dict[str, Any]] = []
    for index, frequency in enumerate(frequencies):
        rows.append(blank_row(
            K_SENSITIVITY_HEADER,
            material=material.name,
            target=target,
            frequency_role="TARGET" if index == 0 else "CONTROL",
            frequency=frequency,
            base_amplitude=base_values[index],
            injected_amplitude=injected_values[index],
            signed_delta=signed[index],
            absolute_delta=absolute[index],
            delta_target=delta_target,
            delta_control=delta_control,
            positive_margin=positive_margin,
            control_margin=control_margin,
            finite=finite,
            face_pass=passed,
        ))
    return KSensitivityFace(
        material.name, target, rows, delta_target, delta_control,
        positive_margin, control_margin, nonfinite_count, finite, passed,
    )


def gate(label: str, passed: bool, disposition: str | None, inputs: dict[str, Any]) -> dict[str, Any]:
    return {
        "disposition": None if passed else disposition,
        "inputs": inputs,
        "label": label,
        "pass": bool(passed),
    }


def evaluated_gate_prefix(specifications: Sequence[tuple[str, bool, str, dict[str, Any]]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for label, passed, disposition, inputs in specifications:
        rows.append(gate(label, passed, disposition, inputs))
        if not passed:
            break
    return rows


def k_raw_rows(
    materials: Sequence[KMaterial],
    expected: dict[int, dict[str, int]],
    comparisons: Sequence[bool],
    pseudo: Sequence[tuple[int | None, bool | None]],
    real_hit: tuple[int | None, bool | None],
    lucky_hit: tuple[int | None, bool | None],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for material in materials:
        usable_set = set(int(index) for index in material.usable)
        for index, center in enumerate(material.centers):
            expected_row = expected.get(index) if material.name == "REAL" else None
            rows.append(blank_row(
                K_RAW_HEADER,
                record="WINDOW",
                material=material.name,
                window_index=index,
                u_center=center,
                count_1mod4=material.count1[index],
                count_3mod4=material.count3[index],
                window_lead=material.lead[index],
                cumulative_lead=material.cumulative[index],
                usable=index in usable_set,
                chi=(material.chi[int(np.searchsorted(material.usable, index))]
                     if index in usable_set else None),
                expected_count_1mod4=(expected_row["count_1mod4"] if expected_row else None),
                expected_count_3mod4=(expected_row["count_3mod4"] if expected_row else None),
                expected_window_lead=(expected_row["window_lead"] if expected_row else None),
                expected_cumulative_lead=(expected_row["cumulative_lead"] if expected_row else None),
                comparison_pass=(comparisons[index] if material.name == "REAL" and index < len(comparisons)
                                 else None),
            ))

    frequencies = K_TARGETS + CONTROLS
    for material in materials:
        for index, frequency in enumerate(frequencies):
            amplitude = material.amplitudes[index]
            rows.append(blank_row(
                K_RAW_HEADER,
                record="AMPLITUDE",
                material=material.name,
                frequency_role="TARGET" if index < len(K_TARGETS) else "CONTROL",
                frequency=frequency,
                amplitude=amplitude,
                control_max=material.control_max,
                margin=(np.float64(amplitude - material.control_max)
                        if amplitude is not None and material.control_max is not None else None),
            ))

    for index, (members, passed) in enumerate(pseudo, 1):
        rows.append(blank_row(
            K_RAW_HEADER,
            record="COMB",
            material="REAL",
            comb_id=f"PSEUDO-{index}",
            members_above=members,
            comb_pass=passed,
        ))
    for material, comb_id, outcome in (
        ("REAL", "REAL-FIRST-3", real_hit),
        ("LUCKY", "LUCKY-FIRST-3", lucky_hit),
    ):
        rows.append(blank_row(
            K_RAW_HEADER,
            record="COMB",
            material=material,
            comb_id=comb_id,
            members_above=outcome[0],
            comb_pass=outcome[1],
        ))
    return rows


def run_arm_k(primes: np.ndarray, luckies: np.ndarray) -> dict[str, Any]:
    minimum_distance, separation_pass = separation_face()
    real = build_k_material("REAL", N_PRIME, primes)
    lucky = build_k_material("LUCKY", N_LUCKY, luckies)
    materials = (real, lucky)
    for material in materials:
        populate_k_amplitudes(material)

    expected, expected_physical_rows, expected_duplicates = load_chebyshev_expected()
    cheb_mismatch, comparisons = compare_chebyshev(real, expected, expected_duplicates)
    cheb_pass = (
        expected_physical_rows == len(expected) == len(real.centers) == 204
        and cheb_mismatch == 0
    )
    empty_pass = real.usable.size > 0 and lucky.usable.size > 0

    base_values = [value for material in materials for value in material.amplitudes if value is not None]
    base_nonfinite = sum(not bool(np.isfinite(value)) for value in base_values)
    numeric_pass = empty_pass and base_nonfinite == 0

    sensitivity_faces = [
        build_k_sensitivity_face(material, target)
        for material in materials
        for target in K_TARGETS[:3]
    ]
    sensitivity_rows = [row for face in sensitivity_faces for row in face.rows]
    sensitivity_nonfinite = sum(face.nonfinite_count for face in sensitivity_faces)
    failed_faces = sum(face.finite and not face.passed for face in sensitivity_faces)
    finite_positive = [face.positive_margin for face in sensitivity_faces if face.finite]
    finite_control = [face.control_margin for face in sensitivity_faces if face.finite]
    minimum_positive = min(finite_positive) if finite_positive else None
    minimum_control = min(finite_control) if finite_control else None
    sensitivity_pass = empty_pass and sensitivity_nonfinite == 0 and failed_faces == 0
    sensitivity_disposition = "INSTRUMENT-SUSPECT" if sensitivity_nonfinite else "INSTRUMENT-INSENSITIVE"

    specifications = (
        ("K-SEPARATION", separation_pass, "INSTRUMENT-SUSPECT", {
            "minimum_distance": json_f(minimum_distance),
            "required_distance": json_f(SEPARATION_REQUIRED),
        }),
        ("K-CHEBYSHEV", cheb_pass, "INSTRUMENT-SUSPECT", {
            "actual_rows": json_i(len(real.centers)),
            "expected_rows": json_i(expected_physical_rows),
            "mismatch_count": json_i(cheb_mismatch),
        }),
        ("K-EMPTY", empty_pass, "INSTRUMENT-INSENSITIVE", {
            "real_usable_count": json_i(real.usable.size),
            "lucky_usable_count": json_i(lucky.usable.size),
        }),
        ("K-NUMERIC", numeric_pass, "INSTRUMENT-SUSPECT", {
            "nonfinite_count": json_i(base_nonfinite),
        }),
        ("K-SENSITIVITY", sensitivity_pass, sensitivity_disposition, {
            "nonfinite_count": json_i(sensitivity_nonfinite),
            "failed_face_count": json_i(failed_faces),
            "minimum_positive_margin": json_f(minimum_positive) if minimum_positive is not None else "",
            "minimum_control_margin": json_f(minimum_control) if minimum_control is not None else "",
        }),
    )
    gates = evaluated_gate_prefix(specifications)

    pseudo = pseudo_comb_results(real)
    real_hit = k_hit(real)
    lucky_hit = k_hit(lucky)
    pseudo_count = sum(bool(result[1]) for result in pseudo if result[1] is not None)
    real_boolean = bool(real_hit[1]) if real_hit[1] is not None else False
    lucky_boolean = bool(lucky_hit[1]) if lucky_hit[1] is not None else False

    partition: dict[str, Any] | None = None
    if all(row["pass"] for row in gates) and len(gates) == len(specifications):
        inputs = {
            "pseudo_comb_pass_count": json_i(pseudo_count),
            "real_hit": real_boolean,
            "lucky_hit": lucky_boolean,
        }
        if pseudo_count > 0 and real_boolean:
            label, disposition, surprise = "K-FP", "INSTRUMENT-SUSPECT", False
        elif lucky_boolean:
            label, disposition, surprise = "K-NONSPECIFIC", None, real_boolean
        elif real_boolean:
            label, disposition, surprise = "K1", None, False
        else:
            label, disposition, surprise = "K2", None, False
        partition = {
            "disposition": disposition,
            "inputs": inputs,
            "label": label,
            "surprise": surprise,
        }

    if partition is None:
        terminal_kind = "GATE"
        terminal_label = gates[-1]["label"]
    else:
        terminal_kind = "ROW"
        terminal_label = partition["label"]

    return {
        "arm": {
            "arm": "K",
            "gates": gates,
            "partition": partition,
            "terminal_kind": terminal_kind,
            "terminal_label": terminal_label,
        },
        "raw_rows": k_raw_rows(materials, expected, comparisons, pseudo, real_hit, lucky_hit),
        "sensitivity_rows": sensitivity_rows,
        "materials": materials,
        "metrics": specifications,
    }


@dataclass
class ODiagnostic:
    label: str
    item_count: int
    mismatch_count: int
    first_mismatch_index: int | None
    mismatch_by_window: np.ndarray | None = None

    @property
    def passed(self) -> bool:
        return self.mismatch_count == 0


@dataclass
class OR8Window:
    window_index: int
    bijection: ODiagnostic
    multiset: ODiagnostic | None
    pair_count: ODiagnostic | None
    ordered_a: np.ndarray | None
    ordered_b: np.ndarray | None

    @property
    def passed(self) -> bool:
        return bool(
            self.bijection.passed
            and self.multiset is not None and self.multiset.passed
            and self.pair_count is not None and self.pair_count.passed
        )


@dataclass
class OOrbit:
    whole_rank: int
    a: int
    b: int
    whole_orbit_count: int

    @property
    def diagonal(self) -> bool:
        return self.a == 1 and self.b == 1


@dataclass
class OCandidate:
    candidate_rank: int
    whole_rank: int
    a: int
    b: int
    present_windows: int
    retained: bool
    real_ab: np.ndarray
    real_ba: np.ndarray
    surrogate_ab: np.ndarray
    surrogate_ba: np.ndarray
    surrogate_available: np.ndarray
    p_real: int | None = None
    m_real: int | None = None
    z_real: int | None = None
    p_surrogate: int | None = None
    m_surrogate: int | None = None
    z_surrogate: int | None = None
    lhs_real: int | None = None
    rhs_real: int | None = None
    lhs_surrogate: int | None = None
    rhs_surrogate: int | None = None
    departs_real: bool | None = None
    departs_surrogate: bool | None = None
    orbit_row: str = "NOT-EVALUATED"


def int64_vector(name: str, values: Any) -> np.ndarray:
    array = np.asarray(values)
    if array.ndim != 1 or array.dtype.kind not in "iu":
        raise ValueError(f"{name} must be a one-dimensional integer array")
    if array.dtype.kind == "u" and array.size and int(array.max()) > np.iinfo(np.int64).max:
        raise ValueError(f"{name} exceeds int64")
    return array.astype(np.int64, copy=False)


def ordered_reduced_pairs(gaps: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    gaps = int64_vector("gaps", gaps)
    if gaps.size < 2:
        return np.empty(0, dtype=np.int64), np.empty(0, dtype=np.int64)
    if np.any(gaps <= 0):
        raise ValueError("Arm O requires positive gaps")
    left, right = gaps[:-1], gaps[1:]
    divisor = np.gcd(left, right)
    return left // divisor, right // divisor


def whole_orbit_ranking(a: np.ndarray, b: np.ndarray) -> list[OOrbit]:
    canonical_a = np.minimum(a, b).astype(np.int64, copy=False)
    canonical_b = np.maximum(a, b).astype(np.int64, copy=False)
    limit = np.iinfo(np.uint32).max
    if canonical_b.size and int(canonical_b.max()) > int(limit):
        raise ValueError("Arm O canonical ratio exceeds uint32 packing hand")
    packed = (canonical_a.astype(np.uint64) << np.uint64(32)) | canonical_b.astype(np.uint64)
    codes, counts = np.unique(packed, return_counts=True)
    decoded_a = (codes >> np.uint64(32)).astype(np.int64)
    decoded_b = (codes & np.uint64(limit)).astype(np.int64)
    counts = counts.astype(np.int64, copy=False)
    order = np.lexsort((decoded_b, decoded_a, -counts))
    return [
        OOrbit(rank, int(decoded_a[index]), int(decoded_b[index]), int(counts[index]))
        for rank, index in enumerate(order[:10], 1)
    ]


def component_diagnostic(
    label: str,
    actual_a: np.ndarray,
    actual_b: np.ndarray,
    expected_a: np.ndarray,
    expected_b: np.ndarray,
    source_indices: np.ndarray | None = None,
    source_windows: np.ndarray | None = None,
    window_count: int | None = None,
) -> ODiagnostic:
    actual_a = int64_vector(f"{label}.actual_a", actual_a)
    actual_b = int64_vector(f"{label}.actual_b", actual_b)
    expected_a = int64_vector(f"{label}.expected_a", expected_a)
    expected_b = int64_vector(f"{label}.expected_b", expected_b)
    if not (actual_a.shape == actual_b.shape == expected_a.shape == expected_b.shape):
        raise ValueError(f"{label} comparison extent differs")
    mismatch = (actual_a != expected_a) | (actual_b != expected_b)
    bad = np.flatnonzero(mismatch)
    if bad.size and source_indices is not None:
        first = int(source_indices[int(bad[0])])
    else:
        first = int(bad[0]) if bad.size else None
    mismatch_by_window = None
    if source_windows is not None:
        if window_count is None:
            raise ValueError(f"{label} window_count missing")
        source_windows = int64_vector(f"{label}.source_windows", source_windows)
        if source_windows.shape != actual_a.shape:
            raise ValueError(f"{label} source-window extent differs")
        mismatch_by_window = np.bincount(
            source_windows[mismatch], minlength=window_count
        ).astype(np.int64)
    return ODiagnostic(label, int(actual_a.size), int(bad.size), first, mismatch_by_window)


def array_diagnostic(label: str, actual: np.ndarray, expected: np.ndarray) -> ODiagnostic:
    actual = int64_vector(f"{label}.actual", actual)
    expected = int64_vector(f"{label}.expected", expected)
    if actual.shape != expected.shape:
        raise ValueError(f"{label} comparison extent differs")
    bad = np.flatnonzero(actual != expected)
    return ODiagnostic(label, int(actual.size), int(bad.size), int(bad[0]) if bad.size else None)


def o_global_diagnostics(
    primes: np.ndarray,
    source_windows: np.ndarray,
    window_count: int,
    original_a: np.ndarray,
    original_b: np.ndarray,
) -> dict[str, ODiagnostic]:
    gaps = np.diff(primes)
    reverse_a, reverse_b = ordered_reduced_pairs(gaps[::-1])
    diagnostics = {
        "O-REVERSAL": component_diagnostic(
            "O-REVERSAL", reverse_a, reverse_b, original_b[::-1], original_a[::-1]
        )
    }
    valid = (source_windows >= 0) & (source_windows < window_count)
    source_indices = np.flatnonzero(valid).astype(np.int64)
    transformed_t = primes + np.int64(1)
    transformed_d = primes * np.int64(2)
    t_gaps, d_gaps = np.diff(transformed_t), np.diff(transformed_d)
    t_a, t_b = ordered_reduced_pairs(t_gaps)
    d_a, d_b = ordered_reduced_pairs(d_gaps)
    diagnostics["O-T-RAW"] = component_diagnostic(
        "O-T-RAW",
        t_gaps[:-1][valid], t_gaps[1:][valid], gaps[:-1][valid], gaps[1:][valid],
        source_indices, source_windows[valid], window_count,
    )
    diagnostics["O-T-REDUCED"] = component_diagnostic(
        "O-T-REDUCED",
        t_a[valid], t_b[valid], original_a[valid], original_b[valid],
        source_indices, source_windows[valid], window_count,
    )
    diagnostics["O-D-REDUCED"] = component_diagnostic(
        "O-D-REDUCED",
        d_a[valid], d_b[valid], original_a[valid], original_b[valid],
        source_indices, source_windows[valid], window_count,
    )
    return diagnostics


def o_r8_window(
    window: int,
    source_gaps: np.ndarray,
    expected_pairs: int,
    r8_permutation: Any,
) -> OR8Window:
    source = int64_vector("O.source_gaps", source_gaps)
    size = int(source.size)
    permutation = int64_vector("O.R8", r8_permutation(size))
    if permutation.size != size:
        raise ValueError("committed R8 violated its declared length-m return")
    expected = np.arange(size, dtype=np.int64)
    bijection = array_diagnostic("O-R8-BIJECTION", np.sort(permutation), expected)
    if not bool(np.all((permutation >= 0) & (permutation < size))):
        return OR8Window(window, bijection, None, None, None, None)
    permuted = source[permutation]
    multiset = array_diagnostic("O-R8-MULTISET", np.sort(permuted), np.sort(source))
    ordered_a, ordered_b = ordered_reduced_pairs(permuted)
    actual_pairs = int(ordered_a.size)
    mismatch = abs(actual_pairs - expected_pairs)
    pair_count = ODiagnostic(
        "O-R8-PAIR-COUNT",
        expected_pairs,
        mismatch,
        min(actual_pairs, expected_pairs) if mismatch else None,
    )
    if not (bijection.passed and multiset.passed and pair_count.passed):
        ordered_a, ordered_b = None, None
    return OR8Window(window, bijection, multiset, pair_count, ordered_a, ordered_b)


def o_counts_by_window(
    pair_a: np.ndarray,
    pair_b: np.ndarray,
    source_windows: np.ndarray,
    valid: np.ndarray,
    window_count: int,
    candidate_a: int,
    candidate_b: int,
) -> tuple[np.ndarray, np.ndarray]:
    ab = valid & (pair_a == candidate_a) & (pair_b == candidate_b)
    ba = valid & (pair_a == candidate_b) & (pair_b == candidate_a)
    return (
        np.bincount(source_windows[ab], minlength=window_count).astype(np.int64),
        np.bincount(source_windows[ba], minlength=window_count).astype(np.int64),
    )


def sign_summary(left: np.ndarray, right: np.ndarray, usable: np.ndarray) -> tuple[int, int, int]:
    signs = np.sign(left[usable] - right[usable])
    positive = int(np.count_nonzero(signs > 0))
    negative = int(np.count_nonzero(signs < 0))
    return positive, negative, int(signs.size - positive - negative)


def finish_o_candidate(candidate: OCandidate, usable: np.ndarray) -> None:
    if not candidate.retained:
        candidate.orbit_row = "DROPPED"
        return
    p, m, z = sign_summary(candidate.real_ab, candidate.real_ba, usable)
    candidate.p_real, candidate.m_real, candidate.z_real = p, m, z
    candidate.lhs_real, candidate.rhs_real = (p - m) ** 2, 9 * (p + m)
    candidate.departs_real = candidate.lhs_real > candidate.rhs_real
    if not bool(np.all(candidate.surrogate_available[usable])):
        return
    p, m, z = sign_summary(candidate.surrogate_ab, candidate.surrogate_ba, usable)
    candidate.p_surrogate, candidate.m_surrogate, candidate.z_surrogate = p, m, z
    candidate.lhs_surrogate, candidate.rhs_surrogate = (p - m) ** 2, 9 * (p + m)
    candidate.departs_surrogate = candidate.lhs_surrogate > candidate.rhs_surrogate
    if candidate.departs_surrogate:
        candidate.orbit_row = "ORBIT-SUSPECT"
    elif candidate.departs_real:
        candidate.orbit_row = "DEPART"
    else:
        candidate.orbit_row = "NULL"


def aggregate_o_r8(label: str, diagnostics: dict[int, OR8Window]) -> ODiagnostic | None:
    selected: list[ODiagnostic] = []
    for window in sorted(diagnostics):
        diagnostic = diagnostics[window]
        value = {
            "O-R8-BIJECTION": diagnostic.bijection,
            "O-R8-MULTISET": diagnostic.multiset,
            "O-R8-PAIR-COUNT": diagnostic.pair_count,
        }[label]
        if value is None:
            return None
        selected.append(value)
    return ODiagnostic(
        label,
        sum(item.item_count for item in selected),
        sum(item.mismatch_count for item in selected),
        None,
    )


def o_gate_prefix(
    globals_: dict[str, ODiagnostic],
    class_set_pass: bool,
    ranked_count: int,
    diagonal_count: int,
    usable_count: int,
    r8: dict[str, ODiagnostic | None],
    retained_count: int,
) -> list[dict[str, Any]]:
    specifications: list[tuple[str, bool, str, dict[str, Any]]] = []
    for label in ("O-REVERSAL", "O-T-RAW", "O-T-REDUCED", "O-D-REDUCED"):
        diagnostic = globals_[label]
        specifications.append((label, diagnostic.passed, "INSTRUMENT-SUSPECT", {
            "compared_count": json_i(diagnostic.item_count),
            "mismatch_count": json_i(diagnostic.mismatch_count),
        }))
    specifications.extend((
        ("O-CLASS-SET", class_set_pass, "INSTRUMENT-SUSPECT", {
            "ranked_count": json_i(ranked_count), "diagonal_count": json_i(diagonal_count),
        }),
        ("O-EMPTY", usable_count > 0, "INSTRUMENT-INSENSITIVE", {
            "usable_count": json_i(usable_count),
        }),
    ))
    for label in ("O-R8-BIJECTION", "O-R8-MULTISET", "O-R8-PAIR-COUNT"):
        diagnostic = r8[label]
        passed = diagnostic is not None and diagnostic.passed
        specifications.append((label, passed, "INSTRUMENT-SUSPECT", {
            "compared_count": json_i(diagnostic.item_count) if diagnostic else "",
            "mismatch_count": json_i(diagnostic.mismatch_count) if diagnostic else "",
        }))
    specifications.append(("O-NO-RETAINED", retained_count > 0, "INSTRUMENT-INSENSITIVE", {
        "retained_count": json_i(retained_count),
    }))
    return evaluated_gate_prefix(specifications)


def o_raw_rows(
    globals_: dict[str, ODiagnostic],
    r8_windows: dict[int, OR8Window],
    usable: np.ndarray,
    candidates: Sequence[OCandidate],
    class_set_pass: bool,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for label in ("O-REVERSAL", "O-T-RAW", "O-T-REDUCED", "O-D-REDUCED"):
        diagnostic = globals_[label]
        rows.append(blank_row(
            O_RAW_HEADER, record="GATE", gate=label, item_count=diagnostic.item_count,
            mismatch_count=diagnostic.mismatch_count,
            first_mismatch_index=diagnostic.first_mismatch_index, **{"pass": diagnostic.passed},
        ))
    for label in ("O-R8-BIJECTION", "O-R8-MULTISET", "O-R8-PAIR-COUNT"):
        for window in usable:
            bundle = r8_windows[int(window)]
            diagnostic = {
                "O-R8-BIJECTION": bundle.bijection,
                "O-R8-MULTISET": bundle.multiset,
                "O-R8-PAIR-COUNT": bundle.pair_count,
            }[label]
            values: dict[str, Any] = {"record": "GATE", "gate": label, "window_index": window}
            if diagnostic is not None:
                values.update(
                    item_count=diagnostic.item_count,
                    mismatch_count=diagnostic.mismatch_count,
                    first_mismatch_index=diagnostic.first_mismatch_index,
                    **{"pass": diagnostic.passed},
                )
            rows.append(blank_row(O_RAW_HEADER, **values))
    if class_set_pass:
        for window in usable:
            index = int(window)
            for candidate in candidates:
                values = dict(
                    record="WINDOW-CLASS", window_index=index,
                    candidate_rank=candidate.candidate_rank, a=candidate.a, b=candidate.b,
                    retained=candidate.retained, real_ab=candidate.real_ab[index],
                    real_ba=candidate.real_ba[index],
                    real_sign=int(np.sign(candidate.real_ab[index] - candidate.real_ba[index])),
                )
                if candidate.surrogate_available[index]:
                    values.update(
                        surrogate_ab=candidate.surrogate_ab[index],
                        surrogate_ba=candidate.surrogate_ba[index],
                        surrogate_sign=int(np.sign(
                            candidate.surrogate_ab[index] - candidate.surrogate_ba[index]
                        )),
                    )
                rows.append(blank_row(O_RAW_HEADER, **values))
    return rows


def o_class_rows(
    ranked: Sequence[OOrbit], candidates: Sequence[OCandidate], class_set_pass: bool,
) -> list[dict[str, Any]]:
    by_whole = {candidate.whole_rank: candidate for candidate in candidates}
    rows: list[dict[str, Any]] = []
    for index in range(10):
        if index >= len(ranked):
            rows.append(blank_row(O_CLASSES_HEADER))
            continue
        orbit = ranked[index]
        values: dict[str, Any] = dict(
            whole_rank=orbit.whole_rank, a=orbit.a, b=orbit.b,
            whole_orbit_count=orbit.whole_orbit_count, diagonal=orbit.diagonal,
        )
        if not class_set_pass:
            values["orbit_row"] = "NOT-EVALUATED"
        elif not orbit.diagonal:
            candidate = by_whole[orbit.whole_rank]
            values.update(
                candidate_rank=candidate.candidate_rank,
                present_windows=candidate.present_windows, retained=candidate.retained,
                p_real=candidate.p_real, m_real=candidate.m_real, z_real=candidate.z_real,
                p_surrogate=candidate.p_surrogate, m_surrogate=candidate.m_surrogate,
                z_surrogate=candidate.z_surrogate, lhs_real=candidate.lhs_real,
                rhs_real=candidate.rhs_real, lhs_surrogate=candidate.lhs_surrogate,
                rhs_surrogate=candidate.rhs_surrogate,
                departs_real=candidate.departs_real,
                departs_surrogate=candidate.departs_surrogate,
                orbit_row=candidate.orbit_row,
            )
        rows.append(blank_row(O_CLASSES_HEADER, **values))
    return rows


def run_arm_o(primes: np.ndarray, r8_permutation: Any) -> dict[str, Any]:
    window_count = n_windows_for(N_PRIME)
    source_windows = window_indices(primes[1:-1])
    gaps = np.diff(primes)
    ordered_a, ordered_b = ordered_reduced_pairs(gaps)
    valid = (source_windows >= 0) & (source_windows < window_count)
    totals = np.bincount(source_windows[valid], minlength=window_count).astype(np.int64)
    usable = np.flatnonzero(totals >= MIN_O_PAIRS).astype(np.int64)
    globals_ = o_global_diagnostics(
        primes, source_windows, window_count, ordered_a, ordered_b
    )
    ranked = whole_orbit_ranking(ordered_a, ordered_b)
    diagonal_count = sum(orbit.diagonal for orbit in ranked)
    class_set_pass = len(ranked) == 10 and diagonal_count == 1

    candidates: list[OCandidate] = []
    if class_set_pass:
        for candidate_rank, orbit in enumerate((item for item in ranked if not item.diagonal), 1):
            real_ab, real_ba = o_counts_by_window(
                ordered_a, ordered_b, source_windows, valid, window_count, orbit.a, orbit.b
            )
            present = int(np.count_nonzero((real_ab[usable] + real_ba[usable]) > 0))
            candidates.append(OCandidate(
                candidate_rank, orbit.whole_rank, orbit.a, orbit.b, present,
                present >= MIN_O_PRESENT_WINDOWS, real_ab, real_ba,
                np.zeros(window_count, dtype=np.int64),
                np.zeros(window_count, dtype=np.int64),
                np.zeros(window_count, dtype=bool),
            ))

    r8_windows: dict[int, OR8Window] = {}
    for window in usable:
        index = int(window)
        lo = int(np.searchsorted(source_windows, index, side="left"))
        hi = int(np.searchsorted(source_windows, index, side="right"))
        bundle = o_r8_window(index, gaps[lo:hi + 1], hi - lo, r8_permutation)
        r8_windows[index] = bundle
        if bundle.passed:
            assert bundle.ordered_a is not None and bundle.ordered_b is not None
            for candidate in candidates:
                candidate.surrogate_ab[index] = np.count_nonzero(
                    (bundle.ordered_a == candidate.a) & (bundle.ordered_b == candidate.b)
                )
                candidate.surrogate_ba[index] = np.count_nonzero(
                    (bundle.ordered_a == candidate.b) & (bundle.ordered_b == candidate.a)
                )
                candidate.surrogate_available[index] = True

    for candidate in candidates:
        finish_o_candidate(candidate, usable)

    aggregates = {
        label: aggregate_o_r8(label, r8_windows)
        for label in ("O-R8-BIJECTION", "O-R8-MULTISET", "O-R8-PAIR-COUNT")
    }
    retained_count = sum(candidate.retained for candidate in candidates)
    gates = o_gate_prefix(
        globals_, class_set_pass, len(ranked), diagonal_count,
        int(usable.size), aggregates, retained_count,
    )
    partition: dict[str, Any] | None = None
    expected_gate_count = 10
    if len(gates) == expected_gate_count and all(item["pass"] for item in gates):
        suspect_count = sum(candidate.orbit_row == "ORBIT-SUSPECT" for candidate in candidates)
        depart_count = sum(candidate.orbit_row == "DEPART" for candidate in candidates)
        if suspect_count:
            label, disposition, surprise = "O-SUSPECT", "INSTRUMENT-SUSPECT", False
        elif depart_count:
            label, disposition, surprise = "O2", None, True
        else:
            label, disposition, surprise = "O1", None, False
        partition = {
            "disposition": disposition,
            "inputs": {
                "orbit_suspect_count": json_i(suspect_count),
                "depart_count": json_i(depart_count),
            },
            "label": label,
            "surprise": surprise,
        }
    terminal_kind = "ROW" if partition is not None else "GATE"
    terminal_label = partition["label"] if partition is not None else gates[-1]["label"]
    return {
        "arm": {
            "arm": "O", "gates": gates, "partition": partition,
            "terminal_kind": terminal_kind, "terminal_label": terminal_label,
        },
        "raw_rows": o_raw_rows(globals_, r8_windows, usable, candidates, class_set_pass),
        "class_rows": o_class_rows(ranked, candidates, class_set_pass),
        "usable_windows": usable,
    }


def normalized_gate(native: dict[str, Any]) -> dict[str, Any]:
    return {
        "disposition": native["disposition"],
        "inputs": json_inputs(native["inputs"]),
        "label": native["label"],
        "pass": bool(native["pass"]),
    }


def arm_s_table_object(result: dict[str, Any]) -> dict[str, Any]:
    gates = [normalized_gate(item) for item in result["evaluated_gates"]]
    native_partition = result["partition"]
    partition = None
    if native_partition is not None:
        partition = {
            "disposition": native_partition["disposition"],
            "inputs": json_inputs(native_partition["inputs"]),
            "label": native_partition["label"],
            "surprise": bool(native_partition["surprise"]),
        }
    return {
        "arm": "S",
        "gates": gates,
        "partition": partition,
        "terminal_kind": "ROW" if partition is not None else "GATE",
        "terminal_label": partition["label"] if partition is not None else gates[-1]["label"],
    }


def table_read_object(
    arm_k: dict[str, Any],
    arm_s: dict[str, Any],
    arm_o: dict[str, Any],
    source_hashes: dict[str, str],
) -> dict[str, Any]:
    return {
        "arms": [arm_k["arm"], arm_s_table_object(arm_s), arm_o["arm"]],
        "plan_sha256": source_hashes[PLAN_REL],
        "schema": "three-arm-table-read-v1",
        "schema_sha256": source_hashes[SCHEMA_REL],
    }


def write_result_artifacts(
    directory: Path,
    arm_k: dict[str, Any],
    arm_s: dict[str, Any],
    arm_o: dict[str, Any],
    source_hashes: dict[str, str],
) -> None:
    write_csv(directory / "k-raw.csv", K_RAW_HEADER, arm_k["raw_rows"])
    write_csv(
        directory / "k-sensitivity.csv",
        K_SENSITIVITY_HEADER,
        arm_k["sensitivity_rows"],
    )
    write_csv(directory / "s-raw.csv", S_RAW_HEADER, arm_s["s_raw_rows"])
    write_csv(directory / "s-algebra.csv", S_ALGEBRA_HEADER, arm_s["s_algebra_rows"])
    write_csv(
        directory / "s-sensitivity.csv",
        S_SENSITIVITY_HEADER,
        arm_s["s_sensitivity_rows"],
    )
    write_csv(directory / "o-raw.csv", O_RAW_HEADER, arm_o["raw_rows"])
    write_csv(directory / "o-classes.csv", O_CLASSES_HEADER, arm_o["class_rows"])
    write_json(
        directory / "table-read.json",
        table_read_object(arm_k, arm_s, arm_o, source_hashes),
    )


def gate_log_lines(arm: dict[str, Any]) -> list[str]:
    lines: list[str] = []
    for item in arm["gates"]:
        label = item["label"]
        lines.append(f"gate.{label}.pass={csv_cell(item['pass'])}")
        lines.append(f"gate.{label}.disposition={item['disposition'] or ''}")
        for metric, value in item["inputs"].items():
            lines.append(f"gate.{label}.{metric}={csv_cell(value)}")
    return lines


def write_run_log(
    directory: Path,
    requested_output: Path,
    commit: str,
    source_hashes: dict[str, str],
    arms: Sequence[dict[str, Any]],
    result_hash: str,
    stage_seconds: Sequence[tuple[str, float]],
    total_seconds: float,
) -> None:
    lines = [
        f"command={shlex.join([sys.executable, *sys.argv])}",
        f"output-dir={requested_output}",
        f"git-commit={commit}",
        "tracked-dirty=false",
    ]
    for rel in SOURCE_RELS:
        lines.append(f"source-sha256.{rel}={source_hashes[rel]}")
    lines.extend((
        f"python-executable={sys.executable}",
        f"python-version={sys.version.replace(os.linesep, ' ')}",
        f"numpy-version={np.__version__}",
        f"platform={platform.platform()}",
        "numpy-build-config.begin",
    ))
    config = numpy_build_config()
    if config:
        lines.extend(config.splitlines())
    lines.append("numpy-build-config.end")
    for arm in arms:
        lines.append(
            f"gate-order.{arm['arm']}=" + ">".join(item["label"] for item in arm["gates"])
        )
    for arm in arms:
        lines.extend(gate_log_lines(arm))
    lines.append(f"result-sha256={result_hash}")
    for name, seconds in stage_seconds:
        lines.append(f"stage-seconds.{name}={seconds:.9f}")
    lines.append(f"total-seconds={total_seconds:.9f}")
    (directory / "run.log").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")


def deterministic_staging_path(requested: Path) -> Path:
    return requested.parent / f".{requested.name}.staging"


@dataclass(frozen=True)
class PreparedSMaterial:
    n64: np.ndarray
    log_p: np.ndarray
    u: np.ndarray
    tau: np.ndarray
    tau_rebased: np.ndarray
    tau_reflected: np.ndarray
    window_index: np.ndarray
    usable_windows: np.ndarray
    bounds: tuple[tuple[int, int], ...]
    permutations: tuple[np.ndarray, ...]


def enumerate_prime_powers(
    primes: np.ndarray, limit: int = N_PRIME
) -> tuple[np.ndarray, np.ndarray]:
    """Return ascending int64 (prime power, base prime) arrays.

    ``primes`` is the runner's ascending int64 sieve result.  Every multiply is
    guarded by ``v <= limit // p`` as required by Amendment IV.
    """

    primes = np.asarray(primes)
    if primes.dtype != np.int64 or primes.ndim != 1:
        raise ValueError("primes must be a one-dimensional int64 array")
    if primes.size and (
        int(primes[0]) < 2
        or int(primes[-1]) > int(limit)
        or np.any(primes[1:] <= primes[:-1])
    ):
        raise ValueError("primes must be strictly ascending in [2, limit]")

    extra_n: list[int] = []
    extra_p: list[int] = []
    for p_value in primes:
        p = int(p_value)
        v = p
        while v <= int(limit) // p:
            v *= p
            extra_n.append(v)
            extra_p.append(p)

    if extra_n:
        n_all = np.concatenate((primes, np.asarray(extra_n, dtype=np.int64)))
        p_all = np.concatenate((primes, np.asarray(extra_p, dtype=np.int64)))
        order = np.argsort(n_all, kind="stable")
        return n_all[order], p_all[order]
    return primes.copy(), primes.copy()


def prepare_s_material(
    n: np.ndarray,
    base_prime: np.ndarray,
    bit_reversal_permutation: Callable[[int], np.ndarray],
) -> PreparedSMaterial:
    n = np.asarray(n)
    base_prime = np.asarray(base_prime)
    if n.dtype != np.int64 or base_prime.dtype != np.int64:
        raise ValueError("prime-power values and base primes must be int64")
    if n.ndim != 1 or base_prime.ndim != 1 or n.shape != base_prime.shape:
        raise ValueError("prime-power arrays must be one-dimensional and aligned")
    if n.size and (
        int(n[0]) < 2
        or int(n[-1]) > N_PRIME
        or np.any(n[1:] <= n[:-1])
    ):
        raise ValueError("prime powers must be strictly ascending in [2, 2^28]")

    # Amendment VII's exact array spelling.
    n64 = n.astype(np.float64)
    p64 = base_prime.astype(np.float64)
    u = np.log(n64)
    log_p = np.log(p64)
    tau = u - U_START
    tau_rebased = u - (U_START + S_LOG_TWO)
    tau_reflected = S_A_TAU - tau

    window_index = np.floor(
        (u - U_START) / WINDOW_WIDTH + np.float64(0.5)
    ).astype(np.int64)
    bounds_by_window: list[tuple[int, int]] = []
    usable: list[int] = []
    for wi in range(S_WINDOW_COUNT):
        lo = int(np.searchsorted(window_index, wi, side="left"))
        hi = int(np.searchsorted(window_index, wi, side="right"))
        if hi - lo >= MIN_S_EVENTS:
            usable.append(wi)
            bounds_by_window.append((lo, hi))

    permutations: list[np.ndarray] = []
    for lo, hi in bounds_by_window:
        permutation = np.asarray(bit_reversal_permutation(hi - lo))
        if permutation.dtype != np.int64 or permutation.ndim != 1:
            raise ValueError("committed R8 must return a one-dimensional int64 array")
        permutations.append(permutation)

    return PreparedSMaterial(
        n64=n64,
        log_p=log_p,
        u=u,
        tau=tau,
        tau_rebased=tau_rebased,
        tau_reflected=tau_reflected,
        window_index=window_index,
        usable_windows=np.asarray(usable, dtype=np.int64),
        bounds=tuple(bounds_by_window),
        permutations=tuple(permutations),
    )


def _frequency_role(fi: int) -> str:
    return "ZETA" if fi < S_ZETA_ARRAY.size else "CONTROL"


def _ordered_finite_max(values: Iterable[np.float64]) -> np.float64 | None:
    values = list(values)
    if not values or any(not bool(np.isfinite(value)) for value in values):
        return None
    answer = np.float64(values[0])
    for value in values[1:]:
        value = np.float64(value)
        if bool(value > answer):
            answer = value
    return answer


def _ordered_extreme_allow_nonfinite(
    values: Iterable[np.float64], *, minimum: bool
) -> np.float64 | None:
    values = [np.float64(value) for value in values]
    if not values:
        return None
    if any(bool(np.isnan(value)) for value in values):
        return np.float64(np.nan)
    if minimum and any(bool(np.isneginf(value)) for value in values):
        return np.float64(-np.inf)
    if not minimum and any(bool(np.isposinf(value)) for value in values):
        return np.float64(np.inf)
    answer = values[0]
    for value in values[1:]:
        if bool(value < answer) if minimum else bool(value > answer):
            answer = value
    return answer


def _sum_with_phase(
    material: PreparedSMaterial,
    weight: np.ndarray,
    phase: np.ndarray,
) -> np.ndarray:
    """Multiply once, then sum each frozen slice in ascending event order."""

    result = np.empty(material.usable_windows.size, dtype=np.complex128)
    terms = weight.astype(np.complex128) * phase
    for ui, (lo, hi) in enumerate(material.bounds):
        result[ui] = np.sum(terms[lo:hi], dtype=np.complex128)
    return result


def _concentrations(
    phasors: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    count = phasors.shape[0]
    concentration = np.empty(count, dtype=np.float64)
    status = np.empty(count, dtype=object)
    numerator = np.empty(count, dtype=np.float64)
    denominator = np.empty(count, dtype=np.float64)
    for fi in range(count):
        numerator[fi] = np.abs(
            np.sum(phasors[fi], dtype=np.complex128)
        )
        denominator[fi] = np.sum(
            np.abs(phasors[fi]), dtype=np.float64
        )
        if bool(denominator[fi] == np.float64(0.0)):
            concentration[fi] = np.float64(0.0)
            status[fi] = NO_MASS
        else:
            concentration[fi] = numerator[fi] / denominator[fi]
            status[fi] = MASS
    return concentration, status, numerator, denominator


def _r8_diag(left: np.ndarray, right: np.ndarray) -> tuple[int, int | None, bool]:
    if left.shape != right.shape:
        common = min(left.size, right.size)
        unequal = np.flatnonzero(left[:common] != right[:common])
        first = int(unequal[0]) if unequal.size else common
        mismatch = int(unequal.size + abs(left.size - right.size))
        return mismatch, first, False
    unequal = np.flatnonzero(left != right)
    mismatch = int(unequal.size)
    first = int(unequal[0]) if unequal.size else None
    return mismatch, first, mismatch == 0


def _r8_bijection(permutation: np.ndarray, m: int) -> tuple[int, int | None, bool]:
    return _r8_diag(
        np.sort(permutation), np.arange(m, dtype=np.int64)
    )


def _r8_multiset(source: np.ndarray, permuted: np.ndarray) -> tuple[int, int | None, bool]:
    source_bits = np.sort(np.ascontiguousarray(source).view(np.uint64))
    permuted_bits = np.sort(np.ascontiguousarray(permuted).view(np.uint64))
    return _r8_diag(source_bits, permuted_bits)


def _separation_gate() -> dict:
    distances: list[np.float64] = []
    for control in S_CONTROLS_ARRAY:
        for comb_frequency in S_UNION_COMB:
            distances.append(
                np.abs(np.float64(control) - np.float64(comb_frequency))
            )
    minimum_distance = _ordered_extreme_allow_nonfinite(distances, minimum=True)
    passed = bool(
        minimum_distance is not None
        and np.isfinite(minimum_distance)
        and minimum_distance >= SEPARATION_REQUIRED
    )
    return {
        "label": "S-SEPARATION",
        "pass": passed,
        "disposition": None if passed else "INSTRUMENT-SUSPECT",
        "inputs": {
            "minimum_distance": minimum_distance,
            "required_distance": SEPARATION_REQUIRED,
        },
    }


def _blank_algebra_row(
    gate: str,
    assertion: str,
    beta: np.float64,
    fi: int,
    compared_count: int,
    *,
    scalar: bool,
) -> dict:
    return {
        "gate": gate,
        "assertion": assertion,
        "beta": beta,
        "frequency_role": _frequency_role(fi),
        "frequency": S_FREQUENCIES_ARRAY[fi],
        "window_index": None,
        "compared_count": compared_count,
        "left_status": NOT_EVALUATED if scalar else None,
        "right_status": NOT_EVALUATED if scalar else None,
        "error": None,
        "scale": None,
        "tolerance": None,
        "mismatch_count": None,
        "first_mismatch_index": None,
        "pass": None,
    }


def _phasor_algebra_row(
    gate: str,
    beta: np.float64,
    fi: int,
    actual: np.ndarray,
    expected: np.ndarray,
    source: np.ndarray,
    available: bool,
) -> dict:
    if not available:
        return _blank_algebra_row(
            gate, "PHASOR", beta, fi, source.size, scalar=False
        )
    residual = np.abs(actual - expected)
    source_scale = np.abs(source)
    error = _ordered_extreme_allow_nonfinite(residual, minimum=False)
    scale = _ordered_extreme_allow_nonfinite(source_scale, minimum=False)
    tolerance = None
    passed = False
    if scale is not None and bool(np.isfinite(scale)):
        floor = np.float64(1.0) if bool(scale < np.float64(1.0)) else scale
        tolerance = np.float64(1e-9) * floor
    if (
        error is not None
        and tolerance is not None
        and bool(np.isfinite(error))
        and bool(error <= tolerance)
    ):
        passed = True
    return {
        "gate": gate,
        "assertion": "PHASOR",
        "beta": beta,
        "frequency_role": _frequency_role(fi),
        "frequency": S_FREQUENCIES_ARRAY[fi],
        "window_index": None,
        "compared_count": int(source.size),
        "left_status": None,
        "right_status": None,
        "error": error,
        "scale": scale,
        "tolerance": tolerance,
        "mismatch_count": None,
        "first_mismatch_index": None,
        "pass": passed,
    }


def _scalar_algebra_row(
    gate: str,
    beta: np.float64,
    fi: int,
    left: np.float64,
    left_status: str,
    right: np.float64,
    right_status: str,
    tolerance: np.float64,
    available: bool,
) -> dict:
    if not available:
        return _blank_algebra_row(gate, "C", beta, fi, 1, scalar=True)
    error = np.abs(np.float64(left) - np.float64(right))
    same_status = left_status == right_status
    finite = bool(np.isfinite(left) and np.isfinite(right) and np.isfinite(error))
    passed = bool(
        same_status
        and finite
        and (
            left_status == NO_MASS
            or (left_status == MASS and error <= tolerance)
        )
    )
    return {
        "gate": gate,
        "assertion": "C",
        "beta": beta,
        "frequency_role": _frequency_role(fi),
        "frequency": S_FREQUENCIES_ARRAY[fi],
        "window_index": None,
        "compared_count": 1,
        "left_status": left_status,
        "right_status": right_status,
        "error": error,
        "scale": None,
        "tolerance": tolerance,
        "mismatch_count": None,
        "first_mismatch_index": None,
        "pass": passed,
    }


def _summarize_numeric_gate(label: str, rows: list[dict]) -> dict:
    failed = sum(row["pass"] is False for row in rows)
    errors = [row["error"] for row in rows if row["error"] is not None]
    margins: list[np.float64] = []
    for row in rows:
        if row["error"] is None or row["tolerance"] is None:
            continue
        if row["left_status"] is not None and not (
            row["left_status"] == MASS and row["right_status"] == MASS
        ):
            continue
        margins.append(np.float64(row["tolerance"]) - np.float64(row["error"]))
    passed = bool(rows and all(row["pass"] is True for row in rows))
    return {
        "label": label,
        "pass": passed,
        "disposition": None if passed else "INSTRUMENT-SUSPECT",
        "inputs": {
            "row_count": len(rows),
            "failed_row_count": failed,
            "maximum_error": _ordered_extreme_allow_nonfinite(errors, minimum=False),
            "minimum_margin": _ordered_extreme_allow_nonfinite(margins, minimum=True),
        },
    }


def _summarize_r8_gate(label: str, rows: list[dict]) -> dict:
    failed = sum(row["pass"] is False for row in rows)
    passed = bool(rows and all(row["pass"] is True for row in rows))
    return {
        "label": label,
        "pass": passed,
        "disposition": None if passed else "INSTRUMENT-SUSPECT",
        "inputs": {
            "row_count": len(rows),
            "failed_row_count": failed,
            "maximum_error": None,
            "minimum_margin": None,
        },
    }


def _r8_row(
    gate: str,
    assertion: str,
    window_index: int,
    compared_count: int,
    mismatch_count: int,
    first_mismatch_index: int | None,
    passed: bool,
    beta: np.float64 | None,
) -> dict:
    return {
        "gate": gate,
        "assertion": assertion,
        "beta": beta,
        "frequency_role": None,
        "frequency": None,
        "window_index": window_index,
        "compared_count": compared_count,
        "left_status": None,
        "right_status": None,
        "error": None,
        "scale": None,
        "tolerance": None,
        "mismatch_count": mismatch_count,
        "first_mismatch_index": first_mismatch_index,
        "pass": passed,
    }


def compute_arm_s(
    n: np.ndarray,
    base_prime: np.ndarray,
    bit_reversal_permutation: Callable[[int], np.ndarray],
) -> dict:
    """Compute Amendment-VII Arm S without serializing or reading results."""

    material = prepare_s_material(n, base_prime, bit_reversal_permutation)
    u_count = int(material.usable_windows.size)
    shape = (S_BETAS_ARRAY.size, S_FREQUENCIES_ARRAY.size, u_count)

    real_s = np.empty(shape, dtype=np.complex128)
    surrogate_s = np.empty(shape, dtype=np.complex128)
    rebased_s = np.empty(shape, dtype=np.complex128)
    reflected_by_source = np.empty(shape, dtype=np.complex128)
    negative_s = np.empty(shape, dtype=np.complex128)

    real_c = np.empty((S_BETAS_ARRAY.size, S_FREQUENCIES_ARRAY.size), dtype=np.float64)
    surrogate_c = np.empty_like(real_c)
    rebased_c = np.empty_like(real_c)
    reflected_c = np.empty_like(real_c)
    negative_c = np.empty_like(real_c)
    real_status = np.empty(real_c.shape, dtype=object)
    surrogate_status = np.empty(real_c.shape, dtype=object)
    rebased_status = np.empty(real_c.shape, dtype=object)
    reflected_status = np.empty(real_c.shape, dtype=object)
    negative_status = np.empty(real_c.shape, dtype=object)

    bijection_diags: list[tuple[int, int | None, bool]] = []
    for (lo, hi), permutation in zip(material.bounds, material.permutations):
        bijection_diags.append(_r8_bijection(permutation, hi - lo))
    multiset_diags: list[list[tuple[int, int | None, bool]]] = [
        [] for _ in range(S_BETAS_ARRAY.size)
    ]

    weights: list[np.ndarray] = []
    surrogate_weights: list[np.ndarray] = []
    surrogate_weight_half: np.ndarray | None = None
    for bi, beta in enumerate(S_BETAS_ARRAY):
        radial = np.power(material.n64, -np.float64(beta))
        weight = material.log_p * radial
        surrogate_weight = weight.copy()
        for ui, ((lo, hi), permutation) in enumerate(
            zip(material.bounds, material.permutations)
        ):
            source = weight[lo:hi]
            permuted = source[permutation]
            surrogate_weight[lo:hi] = permuted
            multiset_diags[bi].append(_r8_multiset(source, permuted))

        weights.append(weight)
        surrogate_weights.append(surrogate_weight)
        if bool(beta == np.float64(0.50)):
            surrogate_weight_half = surrogate_weight

    if surrogate_weight_half is None:
        raise AssertionError("beta 0.50 surrogate was not constructed")
    modulation = np.float64(1.0) + np.float64(0.05) * np.cos(
        np.float64(14.134725) * material.tau
    )
    injected_weight = surrogate_weight_half * modulation
    injected_s = np.empty(
        (S_FREQUENCIES_ARRAY.size, u_count), dtype=np.complex128
    )

    # Phase is beta-independent.  Each position-family/frequency ufunc result
    # is constructed once; REAL and SURROGATE deliberately share phase_tau.
    for fi, frequency in enumerate(S_FREQUENCIES_ARRAY):
        phase_tau = np.exp(
            (np.complex128(-1j) * np.float64(frequency)) * material.tau
        )
        for bi in range(S_BETAS_ARRAY.size):
            real_s[bi, fi] = _sum_with_phase(
                material, weights[bi], phase_tau
            )
            surrogate_s[bi, fi] = _sum_with_phase(
                material, surrogate_weights[bi], phase_tau
            )
        injected_s[fi] = _sum_with_phase(
            material, injected_weight, phase_tau
        )

        phase_rebased = np.exp(
            (np.complex128(-1j) * np.float64(frequency))
            * material.tau_rebased
        )
        for bi in range(S_BETAS_ARRAY.size):
            rebased_s[bi, fi] = _sum_with_phase(
                material, weights[bi], phase_rebased
            )

        phase_reflected = np.exp(
            (np.complex128(-1j) * np.float64(frequency))
            * material.tau_reflected
        )
        for bi in range(S_BETAS_ARRAY.size):
            reflected_by_source[bi, fi] = _sum_with_phase(
                material, weights[bi], phase_reflected
            )

        negative_frequency = np.float64(-np.float64(frequency))
        phase_negative = np.exp(
            (np.complex128(-1j) * negative_frequency) * material.tau
        )
        for bi in range(S_BETAS_ARRAY.size):
            negative_s[bi, fi] = _sum_with_phase(
                material, weights[bi], phase_negative
            )

    for bi in range(S_BETAS_ARRAY.size):
        real_c[bi], real_status[bi], _, _ = _concentrations(real_s[bi])
        surrogate_c[bi], surrogate_status[bi], _, _ = _concentrations(
            surrogate_s[bi]
        )
        rebased_c[bi], rebased_status[bi], _, _ = _concentrations(
            rebased_s[bi]
        )
        # U is ascending, so reflected U is ascending only after reversal.
        reflected_c[bi], reflected_status[bi], _, _ = _concentrations(
            reflected_by_source[bi, :, ::-1]
        )
        negative_c[bi], negative_status[bi], _, _ = _concentrations(
            negative_s[bi]
        )

    nonfinite_count = int(np.count_nonzero(~np.isfinite(real_s)))
    nonfinite_count += int(np.count_nonzero(~np.isfinite(surrogate_s)))
    nonfinite_count += int(np.count_nonzero(~np.isfinite(real_c)))
    nonfinite_count += int(np.count_nonzero(~np.isfinite(surrogate_c)))
    base_numeric_ok = nonfinite_count == 0
    algebra_available = u_count > 0 and base_numeric_ok

    raw_rows: list[dict] = []
    exceedance_counts: dict[str, int | None] = {}
    for face, c_table, status_table in (
        ("REAL", real_c, real_status),
        ("SURROGATE", surrogate_c, surrogate_status),
    ):
        for bi, beta in enumerate(S_BETAS_ARRAY):
            control_max = _ordered_finite_max(c_table[bi, S_ZETA_ARRAY.size :])
            count: int | None = 0 if control_max is not None else None
            for fi, frequency in enumerate(S_FREQUENCIES_ARRAY):
                margin = None
                exceeds = None
                if fi < S_ZETA_ARRAY.size and control_max is not None:
                    if bool(np.isfinite(c_table[bi, fi])):
                        margin = np.float64(c_table[bi, fi]) - control_max
                        exceeds = bool(c_table[bi, fi] > control_max)
                        if exceeds and count is not None:
                            count += 1
                    else:
                        count = None
                raw_rows.append(
                    {
                        "record": "CONCENTRATION",
                        "face": face,
                        "beta": beta,
                        "frequency_role": _frequency_role(fi),
                        "frequency": frequency,
                        "concentration": c_table[bi, fi],
                        "mass_status": status_table[bi, fi],
                        "control_max": control_max,
                        "exceedance_margin": margin,
                        "exceeds_control": exceeds,
                        "exceedance_count": None,
                    }
                )
            if bool(beta == np.float64(0.50)):
                exceedance_counts[face] = count

    for face in ("REAL", "SURROGATE"):
        raw_rows.append(
            {
                "record": "SUMMARY",
                "face": face,
                "beta": np.float64(0.50),
                "frequency_role": None,
                "frequency": None,
                "concentration": None,
                "mass_status": None,
                "control_max": None,
                "exceedance_margin": None,
                "exceeds_control": None,
                "exceedance_count": exceedance_counts.get(face),
            }
        )

    rebase_phasor_rows: list[dict] = []
    rebase_c_rows: list[dict] = []
    reflection_phasor_rows: list[dict] = []
    reflection_c_rows: list[dict] = []
    conjugate_rows: list[dict] = []
    for bi, beta in enumerate(S_BETAS_ARRAY):
        for fi, frequency in enumerate(S_FREQUENCIES_ARRAY):
            rebase_factor = np.exp(
                (np.complex128(1j) * np.float64(frequency)) * S_LOG_TWO
            )
            rebase_expected = rebase_factor * real_s[bi, fi]
            rebase_phasor_rows.append(
                _phasor_algebra_row(
                    "S-REBASE-PHASOR",
                    beta,
                    fi,
                    rebased_s[bi, fi],
                    rebase_expected,
                    real_s[bi, fi],
                    algebra_available,
                )
            )
            rebase_c_rows.append(
                _scalar_algebra_row(
                    "S-REBASE-C",
                    beta,
                    fi,
                    rebased_c[bi, fi],
                    rebased_status[bi, fi],
                    real_c[bi, fi],
                    real_status[bi, fi],
                    np.float64(1e-9),
                    algebra_available,
                )
            )

            reflection_factor = np.exp(
                (np.complex128(-1j) * np.float64(frequency)) * S_A_TAU
            )
            reflection_expected = reflection_factor * np.conjugate(
                real_s[bi, fi]
            )
            reflection_phasor_rows.append(
                _phasor_algebra_row(
                    "S-REFLECTION-PHASOR",
                    beta,
                    fi,
                    reflected_by_source[bi, fi],
                    reflection_expected,
                    real_s[bi, fi],
                    algebra_available,
                )
            )
            reflection_c_rows.append(
                _scalar_algebra_row(
                    "S-REFLECTION-C",
                    beta,
                    fi,
                    reflected_c[bi, fi],
                    reflected_status[bi, fi],
                    real_c[bi, fi],
                    real_status[bi, fi],
                    np.float64(1e-9),
                    algebra_available,
                )
            )
            conjugate_rows.append(
                _scalar_algebra_row(
                    "S-CONJUGATE",
                    beta,
                    fi,
                    real_c[bi, fi],
                    real_status[bi, fi],
                    negative_c[bi, fi],
                    negative_status[bi, fi],
                    np.float64(1e-12),
                    algebra_available,
                )
            )

    surrogate_r8_rows: list[dict] = []
    sensitivity_r8_rows: list[dict] = []
    half_index = int(np.flatnonzero(S_BETAS_ARRAY == np.float64(0.50))[0])
    for ui, (wi, (lo, hi)) in enumerate(
        zip(material.usable_windows, material.bounds)
    ):
        mismatch, first, passed = bijection_diags[ui]
        surrogate_r8_rows.append(
            _r8_row(
                "S-R8-SURROGATE",
                "BIJECTION",
                int(wi),
                hi - lo,
                mismatch,
                first,
                passed,
                None,
            )
        )
        for bi, beta in enumerate(S_BETAS_ARRAY):
            mismatch, first, passed = multiset_diags[bi][ui]
            surrogate_r8_rows.append(
                _r8_row(
                    "S-R8-SURROGATE",
                    "MULTISET",
                    int(wi),
                    hi - lo,
                    mismatch,
                    first,
                    passed,
                    beta,
                )
            )

        mismatch, first, passed = bijection_diags[ui]
        sensitivity_r8_rows.append(
            _r8_row(
                "S-R8-SENSITIVITY",
                "BIJECTION",
                int(wi),
                hi - lo,
                mismatch,
                first,
                passed,
                None,
            )
        )
        mismatch, first, passed = multiset_diags[half_index][ui]
        sensitivity_r8_rows.append(
            _r8_row(
                "S-R8-SENSITIVITY",
                "MULTISET",
                int(wi),
                hi - lo,
                mismatch,
                first,
                passed,
                np.float64(0.50),
            )
        )

    algebra_rows = (
        rebase_phasor_rows
        + rebase_c_rows
        + reflection_phasor_rows
        + reflection_c_rows
        + conjugate_rows
        + surrogate_r8_rows
        + sensitivity_r8_rows
    )

    sensitivity_available = u_count > 0 and base_numeric_ok
    sensitivity_rows: list[dict] = []
    sensitivity_inputs = {
        "one_sided_no_mass_count": 0,
        "nonfinite_count": 0,
        "target_both_no_mass": False,
        "all_controls_both_no_mass": False,
        "delta_target": None,
        "delta_control": None,
        "positive_margin": None,
        "control_margin": None,
    }
    sensitivity_pass = False
    sensitivity_disposition = "INSTRUMENT-INSENSITIVE"
    if sensitivity_available:
        injected_c, injected_status, _, _ = _concentrations(injected_s)
        base_half_c = surrogate_c[half_index]
        base_half_status = surrogate_status[half_index]

        one_sided = 0
        sensitivity_nonfinite = 0
        deltas: list[np.float64 | None] = []
        for fi in range(S_FREQUENCIES_ARRAY.size):
            left_finite = bool(np.isfinite(base_half_c[fi]))
            right_finite = bool(np.isfinite(injected_c[fi]))
            sensitivity_nonfinite += int(not left_finite) + int(not right_finite)
            same_status = base_half_status[fi] == injected_status[fi]
            if not same_status:
                one_sided += 1
            if left_finite and right_finite and same_status:
                deltas.append(
                    np.float64(injected_c[fi]) - np.float64(base_half_c[fi])
                )
            else:
                deltas.append(None)

        target_both_no_mass = bool(
            base_half_status[0] == NO_MASS and injected_status[0] == NO_MASS
        )
        all_controls_both_no_mass = all(
            base_half_status[fi] == NO_MASS and injected_status[fi] == NO_MASS
            for fi in range(S_ZETA_ARRAY.size, S_FREQUENCIES_ARRAY.size)
        )
        delta_target = deltas[0]
        control_delta_values = [
            np.abs(deltas[fi])
            for fi in range(S_ZETA_ARRAY.size, S_FREQUENCIES_ARRAY.size)
            if deltas[fi] is not None
        ]
        delta_control = (
            _ordered_finite_max(control_delta_values)
            if len(control_delta_values) == S_CONTROLS_ARRAY.size
            else None
        )
        positive_margin = delta_target
        control_margin = (
            np.float64(delta_target) - np.float64(delta_control)
            if delta_target is not None and delta_control is not None
            else None
        )
        sensitivity_inputs = {
            "one_sided_no_mass_count": one_sided,
            "nonfinite_count": sensitivity_nonfinite,
            "target_both_no_mass": target_both_no_mass,
            "all_controls_both_no_mass": all_controls_both_no_mass,
            "delta_target": delta_target,
            "delta_control": delta_control,
            "positive_margin": positive_margin,
            "control_margin": control_margin,
        }
        if one_sided or sensitivity_nonfinite:
            sensitivity_disposition = "INSTRUMENT-SUSPECT"
        elif target_both_no_mass or all_controls_both_no_mass:
            sensitivity_disposition = "INSTRUMENT-INSENSITIVE"
        elif delta_target is not None and delta_control is not None:
            sensitivity_pass = bool(
                delta_target > np.float64(0.0)
                and delta_target > delta_control
            )
            sensitivity_disposition = (
                None if sensitivity_pass else "INSTRUMENT-INSENSITIVE"
            )

        global_finite = sensitivity_nonfinite == 0
        for fi, frequency in enumerate(S_FREQUENCIES_ARRAY):
            signed_delta = deltas[fi]
            sensitivity_rows.append(
                {
                    "frequency_role": _frequency_role(fi),
                    "frequency": frequency,
                    "base_concentration": base_half_c[fi],
                    "base_status": base_half_status[fi],
                    "injected_concentration": injected_c[fi],
                    "injected_status": injected_status[fi],
                    "signed_delta": signed_delta,
                    "absolute_delta": (
                        np.abs(signed_delta) if signed_delta is not None else None
                    ),
                    "delta_target": delta_target,
                    "delta_control": delta_control,
                    "positive_margin": positive_margin,
                    "control_margin": control_margin,
                    "finite": global_finite,
                    "gate_pass": sensitivity_pass,
                }
            )
    else:
        for fi, frequency in enumerate(S_FREQUENCIES_ARRAY):
            sensitivity_rows.append(
                {
                    "frequency_role": _frequency_role(fi),
                    "frequency": frequency,
                    "base_concentration": None,
                    "base_status": NOT_EVALUATED,
                    "injected_concentration": None,
                    "injected_status": NOT_EVALUATED,
                    "signed_delta": None,
                    "absolute_delta": None,
                    "delta_target": None,
                    "delta_control": None,
                    "positive_margin": None,
                    "control_margin": None,
                    "finite": None,
                    "gate_pass": None,
                }
            )

    gates = [
        _separation_gate(),
        {
            "label": "S-EMPTY",
            "pass": u_count > 0,
            "disposition": None if u_count > 0 else "INSTRUMENT-INSENSITIVE",
            "inputs": {"usable_count": u_count},
        },
        {
            "label": "S-NUMERIC",
            "pass": base_numeric_ok,
            "disposition": None if base_numeric_ok else "INSTRUMENT-SUSPECT",
            "inputs": {"nonfinite_count": nonfinite_count},
        },
        _summarize_numeric_gate("S-REBASE-PHASOR", rebase_phasor_rows),
        _summarize_numeric_gate("S-REBASE-C", rebase_c_rows),
        _summarize_numeric_gate(
            "S-REFLECTION-PHASOR", reflection_phasor_rows
        ),
        _summarize_numeric_gate("S-REFLECTION-C", reflection_c_rows),
        _summarize_numeric_gate("S-CONJUGATE", conjugate_rows),
        _summarize_r8_gate("S-R8-SURROGATE", surrogate_r8_rows),
        _summarize_r8_gate("S-R8-SENSITIVITY", sensitivity_r8_rows),
        {
            "label": "S-SENSITIVITY",
            "pass": sensitivity_pass,
            "disposition": None if sensitivity_pass else sensitivity_disposition,
            "inputs": sensitivity_inputs,
        },
    ]

    evaluated_gates: list[dict] = []
    for gate in gates:
        evaluated_gates.append(gate)
        if not gate["pass"]:
            break

    partition = None
    if len(evaluated_gates) == len(gates) and all(
        gate["pass"] for gate in evaluated_gates
    ):
        R = int(exceedance_counts["REAL"])
        G = int(exceedance_counts["SURROGATE"])
        if R >= 3 and G == 0:
            label, disposition, surprise = "S1", None, False
        elif R >= 3 and G >= 1:
            label, disposition, surprise = "S-AMB", "AMBIGUOUS", False
        elif R < 3 and G >= 3:
            label, disposition, surprise = (
                "S-SUSPECT",
                "INSTRUMENT-SUSPECT",
                False,
            )
        elif R < 3 and G < 3 and (R >= 1 or G >= 1):
            label, disposition, surprise = "S-WEAK", None, False
        else:
            label, disposition, surprise = "S2", None, False
        partition = {
            "label": label,
            "disposition": disposition,
            "surprise": surprise,
            "inputs": {"R": R, "G": G},
        }

    return {
        "usable_windows": material.usable_windows,
        "s_raw_rows": raw_rows,
        "s_algebra_rows": algebra_rows,
        "s_sensitivity_rows": sensitivity_rows,
        "all_gates": gates,
        "evaluated_gates": evaluated_gates,
        "partition": partition,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    requested = Path(args.out).expanduser().resolve()
    staging = deterministic_staging_path(requested)
    if requested.exists():
        raise FileExistsError(f"output directory already exists: {requested}")
    if staging.exists():
        raise FileExistsError(f"staging directory already exists: {staging}")
    if not requested.parent.is_dir():
        raise FileNotFoundError(f"output parent does not exist: {requested.parent}")

    total_start = time.perf_counter()
    stage_seconds: list[tuple[str, float]] = []

    started = time.perf_counter()
    commit, source_hashes = verify_clean_tracked_sources()
    legacy = load_legacy_module()
    r8_permutation = legacy.bit_reversal_permutation
    lucky_sieve = legacy.lucky_sieve
    stage_seconds.append(("provenance", time.perf_counter() - started))

    staging.mkdir(mode=0o755)
    try:
        started = time.perf_counter()
        primes = sieve_primes(N_PRIME)
        luckies = lucky_sieve(N_LUCKY)
        if primes.dtype != np.int64 or luckies.dtype != np.int64:
            raise TypeError("prime and lucky material must be int64")
        stage_seconds.append(("material", time.perf_counter() - started))

        started = time.perf_counter()
        arm_k = run_arm_k(primes, luckies)
        stage_seconds.append(("K", time.perf_counter() - started))

        started = time.perf_counter()
        prime_powers, base_primes = enumerate_prime_powers(primes)
        arm_s = compute_arm_s(prime_powers, base_primes, r8_permutation)
        stage_seconds.append(("S", time.perf_counter() - started))

        started = time.perf_counter()
        arm_o = run_arm_o(primes, r8_permutation)
        stage_seconds.append(("O", time.perf_counter() - started))

        started = time.perf_counter()
        write_result_artifacts(staging, arm_k, arm_s, arm_o, source_hashes)
        result_hash = canonical_result_hash(staging)
        normalized_s = arm_s_table_object(arm_s)
        arms = (arm_k["arm"], normalized_s, arm_o["arm"])
        stage_seconds.append(("artifacts", time.perf_counter() - started))
        total_seconds = time.perf_counter() - total_start
        write_run_log(
            staging,
            requested,
            commit,
            source_hashes,
            arms,
            result_hash,
            stage_seconds,
            total_seconds,
        )

        expected_names = set(ARTIFACT_NAMES) | {"run.log"}
        actual_names = {entry.name for entry in staging.iterdir()}
        if actual_names != expected_names or any(not entry.is_file() for entry in staging.iterdir()):
            raise RuntimeError(
                f"artifact set differs: expected {sorted(expected_names)}, got {sorted(actual_names)}"
            )
        staging.rename(requested)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
