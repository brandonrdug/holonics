#!/usr/bin/env python3
"""Bounded exact-reference observer for the full 96-coordinate enclosed field junction."""

from __future__ import annotations

import importlib.util
import json
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("passive_reference", HERE / "inspect.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load passive reference")
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)

D = 96
SOURCE_COMPLEX = 32
TARGET_COMPLEX = 16


def bits(value: int) -> int:
    return abs(value).bit_length()


def trunc_div(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("fixed-point denominator must be positive")
    magnitude = abs(numerator) // denominator
    return -magnitude if numerator < 0 else magnitude


def product_shift_zero(left: int, right: int, precision: int) -> int:
    return trunc_div(left * right, 1 << precision)


def scaled_div_zero(numerator: int, denominator: int, precision: int) -> int:
    return trunc_div(numerator * (1 << precision), denominator)


def l1(values: list[int]) -> int:
    return sum(abs(value) for value in values)


def realify(values: list[tuple[Q, Q]]) -> list[Q]:
    return [part for value in values for part in value]


def jrotate(values: list[int]) -> list[int]:
    return [part for index in range(0, len(values), 2) for part in (-values[index + 1], values[index])]


def phase(wire: dict) -> tuple[Q, Q]:
    return Q(wire["real"], wire["denominator"]), Q(
        wire["imaginary"], wire["denominator"]
    )


def fields_from_report(report: dict, limit: int):
    lineages = report.get("body", {}).get("lineage", [])[:limit]
    if not lineages:
        raise ValueError("the report has no field lineages")
    previous = [(Q(0), Q(0)) for _ in lineages[0]["incoming"]]
    fields = []
    arrivals = []
    for lineage in lineages:
        incoming = [phase(value) for value in lineage["incoming"]]
        fields.append([value for pair in zip(previous, incoming) for value in pair])
        arrivals.append(incoming)
        previous = incoming
    return lineages, fields, arrivals


def integer_raw(values: list[tuple[Q, Q]]) -> list[int]:
    result = realify(values)
    if any(value.denominator != 1 for value in result):
        raise ValueError("raw field is not integral in the admitted chart")
    return [value.numerator for value in result]


def exact_anchor_states(report: dict, limit: int) -> list[dict]:
    lineages, fields, arrivals = fields_from_report(report, limit)
    contacts = []
    prefix = [Q(0)] * D
    states = []
    for occurrence, (lineage, field, arrived) in enumerate(zip(lineages, fields, arrivals)):
        source = lineage.get("received_from")
        if source is not None:
            difference = fields[source] + [(-value[0], -value[1]) for value in arrived]
            contacts.append((difference, (Q(0), Q(0)), prefix[:]))
        _step, contacts, v = reference.passive_step(field, contacts)
        sign = Q(-1 if occurrence % 2 else 1)
        prefix = reference.add_vectors(prefix, reference.scale_vector(v, sign))
        h = reference.condensed_h(contacts) if contacts else [Q(0)] * D
        u = realify(field) + [Q(0)] * (2 * TARGET_COMPLEX)
        states.append({"v": v, "outgoing": reference.sub_vectors(v, u), "h": h,
                       "prefix": prefix[:], "contacts": contacts[:], "u": u})
    return states


def outer_add(matrix: list[list[int]], vector: list[int]) -> None:
    for row, left in enumerate(vector):
        for column, right in enumerate(vector):
            matrix[row][column] += left * right


def fixedpoint_ldlt(a: list[list[int]], rhs: list[int], precision: int) -> tuple[list[int], dict]:
    """Mirror enclosed_field_junction.cuh's fixed-point LDL^T path."""
    scale = 1 << precision
    l = [[0] * D for _ in range(D)]
    diagonal = [0] * D
    maximum = product_max = division_max = 0
    for k in range(D):
        correction = 0
        for j in range(k):
            pair = product_shift_zero(l[k][j], l[k][j], precision)
            term = product_shift_zero(pair, diagonal[j], precision)
            product_max = max(product_max, bits(l[k][j] * l[k][j]), bits(pair * diagonal[j]))
            correction += term
        diagonal[k] = a[k][k] * scale - correction
        if diagonal[k] <= 0:
            raise ValueError(f"non-positive fixed-point LDL pivot at {k}")
        maximum = max(maximum, bits(diagonal[k]))
        for i in range(k + 1, D):
            correction_off = 0
            for j in range(k):
                pair = product_shift_zero(l[i][j], l[k][j], precision)
                term = product_shift_zero(pair, diagonal[j], precision)
                product_max = max(product_max, bits(l[i][j] * l[k][j]), bits(pair * diagonal[j]))
                correction_off += term
            numerator = a[i][k] * scale - correction_off
            division_max = max(division_max, bits(numerator * scale))
            l[i][k] = scaled_div_zero(numerator, diagonal[k], precision)
    y = rhs[:]
    solve_product_max = 0
    for i in range(D):
        for j in range(i):
            solve_product_max = max(solve_product_max, bits(l[i][j] * y[j]))
            y[i] -= product_shift_zero(l[i][j], y[j], precision)
    z = [scaled_div_zero(y[i], diagonal[i], precision) for i in range(D)]
    v = [0] * D
    for i in range(D - 1, -1, -1):
        v[i] = z[i]
        for j in range(i + 1, D):
            solve_product_max = max(solve_product_max, bits(l[j][i] * v[j]))
            v[i] -= product_shift_zero(l[j][i], v[j], precision)
    maximum = max(maximum, product_max, division_max, solve_product_max)
    return v, {"dimension": D, "precision_bits": precision,
               "factor_product_max_bits": product_max,
               "factor_division_numerator_max_bits": division_max,
               "solve_product_max_bits": solve_product_max,
               "maximum_intermediate_bits": maximum,
               "signed256_magnitude_bits": 255,
               "fits_signed256_magnitude": maximum <= 255,
               "division": "toward-zero product shifts and divisions; forward retains y, one D division, then backward"}


def sphere_contains(actual: list[Q], centre: list[int], radius: int, scale: int) -> bool:
    error = [value * scale - centre[index] for index, value in enumerate(actual)]
    return sum((value * value for value in error), Q(0)) <= radius * radius


def run_precision(lineages, fields, arrivals, precision: int, anchors: list[dict]) -> dict:
    scale = 1 << precision
    a = [[int(row == column) for column in range(D)] for row in range(D)]
    contacts: list[tuple[list[int], list[int]]] = []
    h = [0] * D
    prefix = [0] * D
    e_h = e_prefix = 0
    maxima = {name: 0 for name in ("E_v", "E_out", "E_hnext", "E_Pnext", "R")}
    exact_checks = {name: 0 for name in ("v", "outgoing", "h", "prefix", "internal", "error_trace")}
    first_256_failure = first_anchor_failure = None
    maximum_ldlt = 0
    selected = []
    for occurrence, (lineage, field, arrived) in enumerate(zip(lineages, fields, arrivals)):
        source = lineage.get("received_from")
        if source is not None:
            d = integer_raw(fields[source]) + [-value for value in integer_raw(arrived)]
            contacts.append((d, prefix[:]))
            outer_add(a, d)
            outer_add(a, jrotate(d))
        u_exact = realify(field) + [Q(0)] * (2 * TARGET_COMPLEX)
        u_scaled = [value * scale for value in u_exact]
        uhat = [int(value) for value in u_scaled]
        e_u = int(sum(abs(value - uhat[index]) for index, value in enumerate(u_scaled)))
        if any(value.denominator != 1 for value in u_scaled):
            e_u = sum((abs(value - uhat[index]).numerator + abs(value - uhat[index]).denominator - 1)
                       // abs(value - uhat[index]).denominator for index, value in enumerate(u_scaled))
        rhs = [2 * (uhat[index] + h[index]) for index in range(D)]
        v, arithmetic = fixedpoint_ldlt(a, rhs, precision)
        maximum_ldlt = max(maximum_ldlt, arithmetic["maximum_intermediate_bits"])
        lhs = [sum(a[row][column] * v[column] for column in range(D)) for row in range(D)]
        residual = [lhs[index] - rhs[index] for index in range(D)]
        R = l1(residual)
        E_v, E_out = 2 * e_h + 2 * e_u + R, 2 * e_h + e_u + R
        E_hnext, E_Pnext = e_h + 2 * e_u + R, e_prefix + E_v
        outgoing = [v[index] - uhat[index] for index in range(D)]
        hnext = [2 * uhat[index] + h[index] - v[index] for index in range(D)]
        pnext = [prefix[index] + (-1 if occurrence % 2 else 1) * v[index] for index in range(D)]
        for name, value in (("E_v", E_v), ("E_out", E_out), ("E_hnext", E_hnext), ("E_Pnext", E_Pnext), ("R", R)):
            maxima[name] = max(maxima[name], value)
        if first_256_failure is None and not arithmetic["fits_signed256_magnitude"]:
            first_256_failure = occurrence
        if occurrence < len(anchors):
            anchor = anchors[occurrence]
            checks = {"v": sphere_contains(anchor["v"], v, E_v, scale),
                      "outgoing": sphere_contains(anchor["outgoing"], outgoing, E_out, scale),
                      "h": sphere_contains(anchor["h"], hnext, E_hnext, scale),
                      "prefix": sphere_contains(anchor["prefix"], pnext, E_Pnext, scale)}
            prior_anchor = anchors[occurrence - 1] if occurrence else None
            prior_h = prior_anchor["h"] if prior_anchor else [Q(0)] * D
            prior_prefix = prior_anchor["prefix"] if prior_anchor else [Q(0)] * D
            error_h = [prior_h[i] * scale - h[i] for i in range(D)]
            delta_u = [u_scaled[i] - uhat[i] for i in range(D)]
            error_v = [anchor["v"][i] * scale - v[i] for i in range(D)]
            trace_rhs = [2 * (error_h[i] + delta_u[i]) - residual[i] for i in range(D)]
            trace_lhs = [sum(a[row][column] * error_v[column] for column in range(D)) for row in range(D)]
            error_hnext = [anchor["h"][i] * scale - hnext[i] for i in range(D)]
            trace_hnext = [error_h[i] + 2 * delta_u[i] - error_v[i] for i in range(D)]
            error_prefix = [anchor["prefix"][i] * scale - pnext[i] for i in range(D)]
            prior_error_prefix = [prior_prefix[i] * scale - prefix[i] for i in range(D)]
            trace_prefix = [prior_error_prefix[i] + (-1 if occurrence % 2 else 1) * error_v[i]
                            for i in range(D)]
            checks["error_trace"] = trace_lhs == trace_rhs and error_hnext == trace_hnext and error_prefix == trace_prefix
            internal_ok = True
            for index, (difference, exact_internal, birth) in enumerate(anchor["contacts"]):
                candidate_d, candidate_birth = contacts[index]
                exact_delta = reference.complexify(reference.sub_vectors(anchor["prefix"], birth))
                exact_b = reference.zsum([reference.zmul(reference.zconj(left), right)
                                          for left, right in zip(difference, exact_delta)])
                sign = Q(-1 if occurrence % 2 else 1)
                exact_b = reference.zscale(exact_b, sign)
                centre_delta = [Q(pnext[i] - candidate_birth[i], scale) for i in range(D)]
                centre_b = reference.zsum([reference.zmul(reference.zconj(left), right)
                                           for left, right in zip(difference, reference.complexify(centre_delta))])
                centre_b = reference.zscale(centre_b, sign)
                error_delta = [(anchor["prefix"][i] - birth[i]) - Q(pnext[i] - candidate_birth[i], scale)
                               for i in range(D)]
                error_b = reference.zsum([reference.zmul(reference.zconj(left), right)
                                          for left, right in zip(difference, reference.complexify(error_delta))])
                error_b = reference.zscale(error_b, sign)
                internal_ok &= exact_b == reference.zadd(centre_b, error_b) == exact_internal
            checks["internal"] = internal_ok
            for name, passed in checks.items():
                exact_checks[name] += passed
            if not all(checks.values()) and first_anchor_failure is None:
                first_anchor_failure = occurrence
        if occurrence in (0, len(lineages) // 2, len(lineages) - 1):
            selected.append({"occurrence": occurrence, "contacts": len(contacts), "R": R, "E_v": E_v,
                             "E_out": E_out, "E_hnext": E_hnext, "E_Pnext": E_Pnext,
                             "ldlt_max_intermediate_bits": arithmetic["maximum_intermediate_bits"]})
        h, prefix, e_h, e_prefix = hnext, pnext, E_hnext, E_Pnext
    return {"precision_bits": precision, "carrier_real_dimension": D, "occurrences": len(lineages),
            "linked_occurrences": len(contacts), "exact_anchor_occurrences": len(anchors),
            "exact_anchor_checks": exact_checks, "first_anchor_failure": first_anchor_failure,
            "maxima_quanta": maxima, "maximum_ldlt_intermediate_bits": maximum_ldlt,
            "first_signed256_failure": first_256_failure, "selected_steps": selected,
            "state": "fixed-point center/radius recurrence after exact anchors; no exact evolving rational state after anchor window"}


def write_new(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    with os.fdopen(descriptor, "w", encoding="utf-8") as output:
        json.dump(value, output, indent=2)
        output.write("\n")


def main() -> None:
    arguments = sys.argv[1:]
    if not arguments:
        raise SystemExit("usage: enclosure.py REPORT --output NEW.json [--occurrences N] [--precisions BITS ...]")
    report_path = Path(arguments.pop(0)); output_path = None; occurrences = 728
    precisions = [12, 24, 48, 72]
    while arguments:
        option = arguments.pop(0)
        if option == "--output" and arguments: output_path = Path(arguments.pop(0))
        elif option == "--occurrences" and arguments: occurrences = int(arguments.pop(0))
        elif option == "--precisions":
            precisions = []
            while arguments and not arguments[0].startswith("--"): precisions.append(int(arguments.pop(0)))
        else: raise SystemExit(f"unknown or incomplete option: {option}")
    if output_path is None or occurrences <= 0 or not precisions or any(value <= 0 for value in precisions):
        raise SystemExit("output, positive occurrences, and positive precision bits are required")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if report.get("profile") != "matched-unit-octet-excitation-native-field":
        raise ValueError("the enclosure requires the matched unit native field report")
    available = min(occurrences, len(report.get("body", {}).get("lineage", [])))
    lineages, fields, arrivals = fields_from_report(report, available)
    anchor_count = min(25, available)
    anchors = exact_anchor_states(report, anchor_count)
    studies = {str(precision): run_precision(lineages, fields, arrivals, precision, anchors)
               for precision in precisions}
    result = {"schema": "holonics.alpha-passive-junction-enclosure.v3",
              "truth_status": "established-bounded",
              "evidence_tags": ["computational-witness"],
              "profile": "passive-junction-fixedpoint-ldlt-enclosure", "input_occurrences": available,
              "exact_anchor_occurrences": anchor_count, "carrier_real_dimension": D,
              "source_complex_dimension": SOURCE_COMPLEX, "target_complex_dimension": TARGET_COMPLEX,
              "precision_bits": precisions, "quantization": "toward zero; floor for nonnegative coordinates",
              "bound_derivation": {"E_v": "2*E_h + 2*E_u + R", "E_out": "2*E_h + E_u + R",
                                   "E_hnext": "E_h + 2*E_u + R", "E_Pnext": "E_P + E_v",
                                   "operator_facts": "||A^-1|| <= 1, ||I-2A^-1|| <= 1, ||2I-2A^-1|| <= 2 for A=I+C"},
              "native_model_or_update_executed": False, "exact_C_from_raw_field": True,
              "covariance_realification": "C = sum(dd^T + Jd(Jd)^T), adjacent real/imag ordering",
              "approximate_h_used_in_C": False, "studies": studies,
              "open_boundary": "Only the first anchor window is exact evolving-rational comparison; the long slice is center/radius arithmetic evidence and makes no productive Athena-alpha claim."}
    write_new(output_path, result)
    print(json.dumps({"schema": result["schema"], "occurrences": available,
                      "exact_anchors": anchor_count, "precisions": precisions,
                      "carrier_real_dimension": D, "native_model_or_update_executed": False}))


if __name__ == "__main__": main()
