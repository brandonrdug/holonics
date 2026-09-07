#!/usr/bin/env python3
"""Certificate checker for the identity-frame enclosed native material report.

This checker never launches native code and never reruns the 96x96 LDL recurrence.  It checks the
packed native centers, residual, radii, source quantization, exact covariance prefix law, and the
first exact anchor window against the independent passive reference.
"""

from __future__ import annotations

import importlib.util
import json
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("enclosure_reference", HERE / "enclosure.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load enclosure reference")
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)
passive = reference.reference

D = 96
STRIDE = D + 1
REPORT_WORDS = 12 * STRIDE


def wide_value(intervals: list[list[int]], index: int) -> int:
    low_entry = intervals[2 * index]
    high_entry = intervals[2 * index + 1]
    if low_entry[0] != low_entry[1] or high_entry[0] != high_entry[1]:
        raise ValueError("native interval is not an exact point")
    low = low_entry[0] & ((1 << 64) - 1)
    high = high_entry[0] & ((1 << 64) - 1)
    value = (high << 64) | low
    return value - (1 << 128) if value >= (1 << 127) else value


def wide_segment(section: dict, part: int) -> list[int]:
    intervals = section["intervals"]
    if section.get("rows") != 1 or section.get("width") != REPORT_WORDS:
        raise ValueError("native enclosed section shape mismatch")
    if len(intervals) != REPORT_WORDS:
        raise ValueError("native enclosed section interval count mismatch")
    return [wide_value(intervals, part * STRIDE + index) for index in range(STRIDE)]


def exact_int_vector(values: list[tuple[Q, Q]]) -> list[int]:
    raw = reference.realify(values)
    if any(value.denominator != 1 for value in raw):
        raise ValueError("raw field is not integral")
    return [value.numerator for value in raw]


def jrotate(values: list[int]) -> list[int]:
    return [part for index in range(0, len(values), 2) for part in (-values[index + 1], values[index])]


def outer_add(matrix: list[list[int]], vector: list[int]) -> None:
    for row, left in enumerate(vector):
        for column, right in enumerate(vector):
            matrix[row][column] += left * right


def ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def rat_vector_distance_squared(actual: list[Q], centre: list[int], scale: int) -> Q:
    return sum(((value - Q(centre[index], scale)) ** 2 for index, value in enumerate(actual)), Q(0))


def run(report: dict) -> dict:
    body = report.get("body", {})
    if report.get("failure") is not None or body.get("pending_lineage") is not None or body.get("observer_error") is not None:
        raise ValueError("native material report did not complete with a certain observed successor")
    representation = body.get("junction_representation", {})
    if report.get("profile") != "matched-unit-octet-field-with-enclosed-junction":
        raise ValueError("wrong serial enclosed-junction profile")
    if representation.get("representation") != "enclosed-dyadic" or representation.get("fractional_bits") != 72:
        raise ValueError("serial report is not the declared 72-bit enclosed representation")
    lineages, fields, arrivals = reference.fields_from_report(report, len(body.get("lineage", [])))
    if any(lineage.get("frame") != 0 for lineage in lineages):
        raise ValueError("this material certificate requires the unrecharted identity source frame")
    history = body.get("junction_history", [])
    if len(lineages) != 728 or len(history) != 728 or report.get("native_occurrences") != 728:
        raise ValueError("serial source/history count is not 728")
    scale = 1 << 72
    covariance = [[0] * D for _ in range(D)]
    prior_h = [0] * D
    prior_prefix = [0] * D
    prior_radius_h = prior_radius_prefix = 0
    birth_prefixes: list[list[int]] = []
    birth_radii: list[int] = []
    part_starts = {entry.get("native_from") for entry in report.get("part_native_ranges", [])}
    counts = {name: 0 for name in (
        "sections", "source_centers", "residuals", "center_recurrences", "radii",
        "source_boundaries", "exact_balls", "birth_internal_balls")}
    failures = []
    exact_anchors = reference.exact_anchor_states(report, 25)
    first25_internal_total = first25_internal_pass = 0

    for occurrence, (lineage, field, arrived, entry) in enumerate(
        zip(lineages, fields, arrivals, history)
    ):
        if entry[0] != occurrence:
            failures.append(f"history occurrence {entry[0]} at position {occurrence}")
            continue
        section = entry[1]
        try:
            values = [wide_segment(section, part) for part in range(6)]
        except ValueError as error:
            failures.append(f"occurrence {occurrence}: {error}")
            continue
        counts["sections"] += 1
        v, outgoing, h, prefix, uhat, residual = values
        source_exact = reference.realify(field) + [Q(0)] * 32
        expected_uhat = [int(value * scale) for value in source_exact]
        if uhat[:D] == expected_uhat and uhat[D] == 0:
            counts["source_centers"] += 1
        else:
            failures.append(f"occurrence {occurrence}: Uhat mismatch")
        e_u = sum(abs(value * scale - expected_uhat[index]) for index, value in enumerate(source_exact))
        if uhat[D] != e_u:
            failures.append(f"occurrence {occurrence}: source-error bound mismatch")
        source = lineage.get("received_from")
        if occurrence in part_starts:
            if source is not None:
                failures.append(f"occurrence {occurrence}: part start has a source link")
        elif source != occurrence - 1:
            failures.append(f"occurrence {occurrence}: within-part source is not predecessor")
        if source is not None:
            d = exact_int_vector(fields[source]) + [-value for value in exact_int_vector(arrived)]
            outer_add(covariance, d)
            outer_add(covariance, jrotate(d))
            birth_prefixes.append(prior_prefix[:])
            birth_radii.append(prior_radius_prefix)
        cden = 1
        a_num = [[covariance[row][column] + int(row == column) for column in range(D)] for row in range(D)]
        expected_residual = [
            sum(a_num[row][column] * v[column] for column in range(D))
            - 2 * (uhat[row] + prior_h[row])
            for row in range(D)
        ]
        if residual[:D] == expected_residual and residual[D] == cden:
            counts["residuals"] += 1
        else:
            failures.append(f"occurrence {occurrence}: exact residual mismatch")
        expected_out = [v[index] - uhat[index] for index in range(D)]
        expected_h = [2 * uhat[index] + prior_h[index] - v[index] for index in range(D)]
        expected_prefix = [prior_prefix[index] + (-1 if occurrence % 2 else 1) * v[index] for index in range(D)]
        if outgoing[:D] == expected_out and h[:D] == expected_h and prefix[:D] == expected_prefix:
            counts["center_recurrences"] += 1
        else:
            failures.append(f"occurrence {occurrence}: center recurrence mismatch")
        residual_radius = ceil_div(sum(abs(value) for value in expected_residual), cden)
        radius_v, radius_out, radius_h, radius_prefix = [values[part][D] for part in range(4)]
        if (radius_v == 2 * prior_radius_h + 2 * e_u + residual_radius
                and radius_out == 2 * prior_radius_h + e_u + residual_radius
                and radius_h == prior_radius_h + 2 * e_u + residual_radius
                and radius_prefix == prior_radius_prefix + radius_v):
            counts["radii"] += 1
        else:
            failures.append(f"occurrence {occurrence}: radius recurrence mismatch")
        if occurrence < 25:
            anchor = exact_anchors[occurrence]
            exact_balls = [
                (anchor["v"], v, radius_v), (anchor["outgoing"], outgoing, radius_out),
                (anchor["h"], h, radius_h), (anchor["prefix"], prefix, radius_prefix)]
            if all(rat_vector_distance_squared(actual, centre, scale) <= Q(radius * radius, scale * scale)
                   for actual, centre, radius in exact_balls):
                counts["exact_balls"] += 1
            else:
                failures.append(f"occurrence {occurrence}: exact center ball failure")
            for contact_index, (difference, exact_internal, birth) in enumerate(anchor["contacts"]):
                first25_internal_total += 1
                d_norm_squared = sum(
                    value[0] * value[0] + value[1] * value[1] for value in difference
                )
                native_birth = birth_prefixes[contact_index]
                birth_radius = birth_radii[contact_index]
                centre_delta = [Q(prefix[index] - native_birth[index], scale)
                                for index in range(D)]
                centre_internal = passive.zsum([
                    passive.zmul(passive.zconj(left), right)
                    for left, right in zip(difference, passive.complexify(centre_delta))])
                centre_internal = passive.zscale(centre_internal, Q(-1 if occurrence % 2 else 1))
                # Avoid floating point: compare squared distance against ||d||² times the
                # squared sum of the current and birth prefix radii.
                radius_bound_squared = Q(d_norm_squared) * Q((radius_prefix + birth_radius) ** 2, scale * scale)
                distance_squared = (exact_internal[0] - centre_internal[0]) ** 2 + (exact_internal[1] - centre_internal[1]) ** 2
                if distance_squared <= radius_bound_squared:
                    first25_internal_pass += 1
            counts["birth_internal_balls"] = first25_internal_pass
        prior_h, prior_prefix = h[:D], prefix[:D]
        prior_radius_h, prior_radius_prefix = radius_h, radius_prefix

    covariance_section = body.get("junction_covariance", {})
    cov_intervals = covariance_section.get("intervals", [])
    final_cov_den = cov_intervals[-1][0] if cov_intervals else 0
    covariance_match = len(cov_intervals) == D * D + 1 and final_cov_den == 1
    if covariance_match:
        covariance_match = all(interval[0] == interval[1] == covariance[row][column]
                               for row in range(D) for column in range(D)
                               for interval in [cov_intervals[row * D + column]])
    if covariance_match:
        counts["final_covariance"] = 1
    else:
        failures.append("final native covariance mismatch")
    counts["residual_covariance_prefixes"] = counts["residuals"]
    ranges = report.get("part_native_ranges", [])
    source_coordinates = report.get("source_part_coordinates", [])
    boundary_ok = bool(ranges) and len(ranges) == len(source_coordinates) and ranges[0].get("native_from") == 0
    for previous, current in zip(ranges, ranges[1:]):
        boundary_ok &= previous.get("native_until") == current.get("native_from") and previous.get("complete") is True
    boundary_ok &= ranges[-1].get("native_until") == 728 and ranges[-1].get("complete") is True
    if boundary_ok:
        counts["source_boundaries"] = len(ranges)
    else:
        failures.append("source part boundary mismatch")
    counts["birth_internal_balls"] = first25_internal_pass if first25_internal_total else counts["birth_internal_balls"]
    if first25_internal_pass != first25_internal_total:
        failures.append(f"internal-current containment: {first25_internal_pass}/{first25_internal_total}")
    return {
        "truth_status": "established-bounded",
        "evidence_tags": ["computational-witness", "measured"],
        "profile": report["profile"],
        "native_occurrences": 728,
        "carrier_real_dimension": D,
        "fractional_bits": 72,
        "checks": counts,
        "first25_internal_current_checks": {"passed": first25_internal_pass, "total": first25_internal_total},
        "all_certificate_checks_pass": not failures and first25_internal_pass == first25_internal_total,
        "failure_count": len(failures),
        "failures": failures[:20],
        "native_exact_point_equality_claim_after_anchor_window": False,
        "native_model_or_update_executed": False,
    }


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[2] != "--output":
        raise SystemExit("usage: verify_native.py REPORT --output NEW.json")
    report_path = Path(sys.argv[1])
    result = run(json.loads(report_path.read_text(encoding="utf-8")))
    output = Path(sys.argv[3])
    output.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(output, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"schema": "holonics.alpha-passive-junction-native-certificate.v1",
                      "native_occurrences": 728, "all_certificate_checks_pass": result["all_certificate_checks_pass"],
                      "native_model_or_update_executed": False}))
    if not result["all_certificate_checks_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
