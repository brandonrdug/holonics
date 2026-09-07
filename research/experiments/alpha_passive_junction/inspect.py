#!/usr/bin/env python3
"""Exact CPU observer for the proposed coupled passive junction.

This script reads native field lineages already recorded by the private AC1 report. It does not
run native code, modify a model, select a response, or write to the repository. The octet/current
codec and the resident field remain separate: this observer consumes the actual recorded full
fields and actual source-handle indices.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as Q
from math import gcd
from pathlib import Path


Complex = tuple[Q, Q]


def zzero() -> Complex:
    return Q(0), Q(0)


def zadd(a: Complex, b: Complex) -> Complex:
    return a[0] + b[0], a[1] + b[1]


def zsub(a: Complex, b: Complex) -> Complex:
    return a[0] - b[0], a[1] - b[1]


def zmul(a: Complex, b: Complex) -> Complex:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def zconj(a: Complex) -> Complex:
    return a[0], -a[1]


def zscale(a: Complex, c: Q) -> Complex:
    return c * a[0], c * a[1]


def zsum(values: list[Complex]) -> Complex:
    result = zzero()
    for value in values:
        result = zadd(result, value)
    return result


def znorm2(a: Complex) -> Q:
    return a[0] * a[0] + a[1] * a[1]


def qwire(value: Q) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def bit_width(value: int) -> int:
    return abs(value).bit_length()


def phase(wire: dict) -> Complex:
    return Q(wire["real"], wire["denominator"]), Q(
        wire["imaginary"], wire["denominator"]
    )


def realify(values: list[Complex]) -> list[Q]:
    return [part for value in values for part in value]


def complexify(values: list[Q]) -> list[Complex]:
    if len(values) % 2:
        raise ValueError("realification has an odd extent")
    return list(zip(values[::2], values[1::2]))


def jrotate(values: list[Q]) -> list[Q]:
    rotated: list[Q] = []
    for index in range(0, len(values), 2):
        rotated.extend((-values[index + 1], values[index]))
    return rotated


def dot(left: list[Q], right: list[Q]) -> Q:
    if len(left) != len(right):
        raise ValueError("dot product extent mismatch")
    return sum((a * b for a, b in zip(left, right)), Q(0))


def outer_add(matrix: list[list[Q]], vector: list[Q]) -> None:
    for row, left in enumerate(vector):
        for column, right in enumerate(vector):
            matrix[row][column] += left * right


def mat_vec(matrix: list[list[Q]], vector: list[Q]) -> list[Q]:
    return [dot(row, vector) for row in matrix]


def add_vectors(left: list[Q], right: list[Q]) -> list[Q]:
    return [a + b for a, b in zip(left, right)]


def sub_vectors(left: list[Q], right: list[Q]) -> list[Q]:
    return [a - b for a, b in zip(left, right)]


def scale_vector(vector: list[Q], scalar: Q) -> list[Q]:
    return [scalar * value for value in vector]


def lcm(left: int, right: int) -> int:
    return abs(left // gcd(left, right) * right)


def integerize_system(matrix: list[list[Q]], rhs: list[Q]) -> tuple[list[list[int]], list[int], int]:
    """Clear one exact common denominator from a rational linear system."""
    denominator = 1
    for row in matrix:
        for value in row:
            denominator = lcm(denominator, value.denominator)
    for value in rhs:
        denominator = lcm(denominator, value.denominator)
    integer_matrix = [
        [value.numerator * (denominator // value.denominator) for value in row]
        for row in matrix
    ]
    integer_rhs = [value.numerator * (denominator // value.denominator) for value in rhs]
    return integer_matrix, integer_rhs, denominator


def normalized_integer_matrix(matrix: list[list[Q]]) -> tuple[list[list[int]], int]:
    """Return the native-style globally reduced numerator matrix and its denominator."""
    integer_matrix, _zero_rhs, denominator = integerize_system(matrix, [Q(0)])
    divisor = denominator
    for row in integer_matrix:
        for value in row:
            divisor = gcd(divisor, abs(value))
    if divisor > 1:
        integer_matrix = [[value // divisor for value in row] for row in integer_matrix]
        denominator //= divisor
    return integer_matrix, denominator


def normalized_integer_vector(vector: list[Q]) -> tuple[list[int], int]:
    """Return the native-style globally reduced numerator vector and its denominator."""
    integer_matrix, integer_vector, denominator = integerize_system([], vector)
    del integer_matrix
    divisor = denominator
    for value in integer_vector:
        divisor = gcd(divisor, abs(value))
    if divisor > 1:
        integer_vector = [value // divisor for value in integer_vector]
        denominator //= divisor
    return integer_vector, denominator


def bareiss_solve(
    matrix: list[list[int]], rhs: list[Q], *, native_adjugate: bool = False
) -> tuple[list[Q], dict]:
    """Solve an exact integer system and retain predivision aperture testimony."""
    size = len(matrix)
    if size == 0:
        return [], {"dimension": 0, "max_intermediate_bits": 0, "max_rhs_bits": 0}
    if any(len(row) != size for row in matrix) or len(rhs) != size:
        raise ValueError("Bareiss shape mismatch")
    denominator = 1
    for value in rhs:
        denominator = lcm(denominator, value.denominator)
    augmented = [row[:] + [int(value * denominator)] for row, value in zip(matrix, rhs)]
    maximum = max((bit_width(value) for row in augmented for value in row), default=0)
    maximum_product = 0
    maximum_subtraction = 0
    maximum_predivision = maximum
    previous = 1
    pivot_bits: list[int] = []
    for pivot_at in range(size - 1):
        pivot_row = next(
            (row for row in range(pivot_at, size) if augmented[row][pivot_at] != 0), None
        )
        if pivot_row is None:
            raise ValueError("singular passive junction system")
        if pivot_row != pivot_at:
            augmented[pivot_at], augmented[pivot_row] = augmented[pivot_row], augmented[pivot_at]
        pivot = augmented[pivot_at][pivot_at]
        pivot_bits.append(bit_width(pivot))
        for row in range(pivot_at + 1, size):
            factor = augmented[row][pivot_at]
            for column in range(pivot_at + 1, size + 1):
                left_product = augmented[row][column] * pivot
                right_product = factor * augmented[pivot_at][column]
                numerator = left_product - right_product
                maximum_product = max(maximum_product, bit_width(left_product), bit_width(right_product))
                maximum_subtraction = max(maximum_subtraction, bit_width(numerator))
                maximum_predivision = max(maximum_predivision, maximum_product, maximum_subtraction)
                if numerator % previous:
                    raise ValueError("Bareiss division left a remainder")
                augmented[row][column] = numerator // previous
            augmented[row][pivot_at] = 0
        previous = pivot
        maximum = max(maximum, max(bit_width(value) for row in augmented for value in row))
    pivot = augmented[-1][-2]
    if pivot == 0:
        raise ValueError("singular passive junction terminal pivot")
    pivot_bits.append(bit_width(pivot))
    determinant = augmented[-1][-2]
    backsub_product = 0
    backsub_subtraction = 0
    if native_adjugate:
        adjugate_numerators_int = [0 for _ in range(size)]
        for row in range(size - 1, -1, -1):
            numerator = augmented[row][-1] * determinant
            backsub_product = max(backsub_product, bit_width(numerator))
            for column in range(row + 1, size):
                product = augmented[row][column] * adjugate_numerators_int[column]
                backsub_product = max(backsub_product, bit_width(product))
                numerator -= product
                backsub_subtraction = max(backsub_subtraction, bit_width(numerator))
            diagonal = augmented[row][row]
            if diagonal == 0 or numerator % diagonal:
                raise ValueError("native adjugate backsubstitution left a remainder")
            adjugate_numerators_int[row] = numerator // diagonal
        solution = [Q(value, determinant * denominator) for value in adjugate_numerators_int]
        adjugate_numerators = [Q(value) for value in adjugate_numerators_int]
    else:
        solution_scaled = [Q(0) for _ in range(size)]
        for row in range(size - 1, -1, -1):
            remainder = Q(augmented[row][-1]) - sum(
                (augmented[row][column] * solution_scaled[column] for column in range(row + 1, size)),
                Q(0),
            )
            solution_scaled[row] = remainder / augmented[row][row]
        solution = [value / denominator for value in solution_scaled]
        adjugate_numerators = [value * determinant for value in solution_scaled]
    return solution, {
        "dimension": size,
        "rhs_common_denominator_bits": bit_width(denominator),
        "max_intermediate_bits": maximum,
        "max_product_bits_before_division": maximum_product,
        "max_subtraction_bits_before_division": maximum_subtraction,
        "max_predivision_bits": maximum_predivision,
        "max_adjugate_backsub_product_bits": backsub_product,
        "max_adjugate_backsub_subtraction_bits": backsub_subtraction,
        "max_pivot_bits": max(pivot_bits, default=0),
        "determinant_bits": bit_width(determinant),
        "adjugate_equivalent_numerator_bits": max(
            (bit_width(value.numerator) for value in adjugate_numerators), default=0
        ),
        "native_adjugate_backsub": native_adjugate,
        "reduced_numerator_bits": max((bit_width(value.numerator) for value in solution), default=0),
        "reduced_denominator_bits": max((bit_width(value.denominator) for value in solution), default=0),
        "i128_signed_magnitude_bits": 127,
        "fits_i128_predivision": maximum_predivision <= 127,
    }


def contact_vectors(difference: list[Complex]) -> tuple[list[Q], list[Q]]:
    real = realify(difference)
    return real, jrotate(real)


def matrix_from_contacts(contacts: list[tuple[list[Q], list[Q]]], dimension: int) -> list[list[Q]]:
    matrix = [[Q(int(row == column)) for column in range(dimension)] for row in range(dimension)]
    for real, imaginary in contacts:
        outer_add(matrix, real)
        outer_add(matrix, imaginary)
    return matrix


def condensed_h(contacts: list[tuple[list[Complex], Complex, list[Q]]]) -> list[Q]:
    result = [Q(0) for _ in range(len(contacts[0][0]) * 2)] if contacts else []
    for difference, internal, _birth_prefix in contacts:
        contribution = [zmul(value, internal) for value in difference]
        result = add_vectors(result, realify(contribution))
    return result


def passive_step(
    q_now: list[Complex],
    contacts: list[tuple[list[Complex], Complex, list[Q]]],
    observe_full_matrix: bool = False,
) -> tuple[dict, list[tuple[list[Complex], Complex, list[Q]]], list[Q]]:
    """Apply the proposed passive junction with exact realification and energy balance."""
    source_dimension = len(q_now)
    difference_dimension = source_dimension + len(q_now) // 2
    full_contacts = [
        contact_vectors(difference)
        for difference, _internal, _birth_prefix in contacts
    ]
    matrix = matrix_from_contacts(full_contacts, difference_dimension * 2)
    q_real = realify(q_now)
    u = q_real + [Q(0) for _ in range(len(q_now))]
    h = condensed_h(contacts)
    if not h:
        h = [Q(0) for _ in u]
    rhs = scale_vector(add_vectors(u, h), Q(2))
    # U Uᵀ is the realification of the contact moment. Woodbury reduces the exact solve to
    # the contact rank while preserving the full matrix equation A v = 2(u+h).
    columns: list[list[Q]] = []
    for real, imaginary in full_contacts:
        columns.extend((real, imaginary))
    if columns:
        gram = [
            [Q(int(row == column)) + dot(columns[row], columns[column]) for column in range(len(columns))]
            for row in range(len(columns))
        ]
        projected = [dot(column, rhs) for column in columns]
        gram_integer, projected_integer, gram_scale = integerize_system(gram, projected)
        correction, bareiss = bareiss_solve(gram_integer, [Q(value) for value in projected_integer])
        bareiss["system_common_denominator_bits"] = bit_width(gram_scale)
        bareiss["algorithm"] = "integer-scaled Woodbury contact-rank system"
        v = rhs[:]
        for column, coefficient in zip(columns, correction):
            v = sub_vectors(v, scale_vector(column, coefficient))
    else:
        bareiss = {"dimension": 0, "max_intermediate_bits": 0, "max_pivot_bits": 0,
                   "reduced_numerator_bits": max((bit_width(value.numerator) for value in rhs), default=0),
                   "reduced_denominator_bits": max((bit_width(value.denominator) for value in rhs), default=0),
                   "rhs_common_denominator_bits": max((bit_width(value.denominator) for value in rhs), default=0),
                   "max_product_bits_before_division": 0,
                   "max_subtraction_bits_before_division": 0,
                   "max_predivision_bits": 0,
                   "i128_signed_magnitude_bits": 127, "fits_i128_predivision": True}
        bareiss["system_common_denominator_bits"] = 0
        bareiss["algorithm"] = "identity system"
        v = rhs
    full_bareiss = None
    if observe_full_matrix:
        # Match the device helper's staging: C is normalized independently as C_num/C_den;
        # only the combined current RHS receives rhs_den before Bareiss.  Scaling A by rhs_den
        # would measure a different arithmetic path and is intentionally excluded here.
        identity = [[Q(int(row == column)) for column in range(len(matrix))] for row in range(len(matrix))]
        covariance = [
            [matrix[row][column] - identity[row][column] for column in range(len(matrix))]
            for row in range(len(matrix))
        ]
        covariance_num, covariance_den = normalized_integer_matrix(covariance)
        u_num, u_den = normalized_integer_vector(u)
        h_num, h_den = normalized_integer_vector(h)
        rhs_den = lcm(u_den, h_den)
        combined = [
            u_num[index] * (rhs_den // u_den) + h_num[index] * (rhs_den // h_den)
            for index in range(len(u))
        ]
        native_matrix = [row[:] for row in covariance_num]
        for index in range(len(native_matrix)):
            native_matrix[index][index] += covariance_den
        native_rhs = [2 * covariance_den * value for value in combined]
        native_v, full_bareiss = bareiss_solve(
            native_matrix, [Q(value) for value in native_rhs], native_adjugate=True
        )
        full_v = [value / rhs_den for value in native_v]
        if full_v != v:
            raise ValueError("full matrix and Woodbury passive solves disagree")
        full_bareiss["covariance_denominator_bits"] = bit_width(covariance_den)
        full_bareiss["rhs_denominator_bits"] = bit_width(rhs_den)
        full_bareiss["native_matrix_diagonal_denominator_bits"] = bit_width(covariance_den)
        full_bareiss["algorithm"] = (
            "native C_num + C_den I; RHS-only rhs_den scaling; fraction-free Bareiss "
            "with integer adjugate backsubstitution"
        )
    if mat_vec(matrix, v) != rhs:
        raise ValueError("exact passive junction solve failed")
    matrix_current = sub_vectors(mat_vec(matrix, v), v)
    direct_current = [Q(0) for _ in v]
    v_complex = complexify(v)
    for difference, _internal, _birth_prefix in contacts:
        projected_value = zsum(
            [zmul(zconj(left), right) for left, right in zip(difference, v_complex)]
        )
        direct_current = add_vectors(
            direct_current,
            realify([zmul(left, projected_value) for left in difference]),
        )
    if matrix_current != direct_current:
        raise ValueError("realified C disagrees with the complex paired moment")
    outgoing = sub_vectors(v, u)
    b_next: list[tuple[list[Complex], Complex]] = []
    for difference, internal, birth_prefix in contacts:
        projected_value = zsum(
            [zmul(zconj(left), right) for left, right in zip(difference, v_complex)]
        )
        b_next.append((difference, zsub(projected_value, internal), birth_prefix))
    h_next = condensed_h(b_next) if b_next else []
    expected_h = sub_vectors(matrix_current, h) if b_next else []
    if h_next != expected_h:
        raise ValueError("condensed internal current disagrees with C v - h")
    norm_left = sum((value * value for value in u), Q(0)) + sum(
        (znorm2(internal) for _difference, internal, _birth_prefix in contacts), Q(0)
    )
    norm_right = sum((value * value for value in outgoing), Q(0)) + sum(
        (znorm2(internal) for _difference, internal, _birth_prefix in b_next), Q(0)
    )
    if norm_left != norm_right:
        raise ValueError("weighted passive norm balance failed")
    return {
        "dimension": len(v),
        "contacts": len(contacts),
        "realification_verified": True,
        "weighted_norm_balance": True,
        "h_identity": True,
        "bareiss": bareiss,
        "full_matrix_bareiss": full_bareiss,
        "reduced_v_numerator_bits": max((bit_width(value.numerator) for value in v), default=0),
        "reduced_v_denominator_bits": max((bit_width(value.denominator) for value in v), default=0),
        "reduced_outgoing_numerator_bits": max((bit_width(value.numerator) for value in outgoing), default=0),
        "reduced_outgoing_denominator_bits": max((bit_width(value.denominator) for value in outgoing), default=0),
        "alternating_decoder_verified": None,
    }, b_next, v


def synthetic_checks() -> dict:
    first = [(Q(1), Q(0)), (Q(0), Q(0))]
    second = [(Q(-1), Q(0)), (Q(0), Q(0))]
    linear_sum = [zadd(a, b) for a, b in zip(first, second)]
    moments = matrix_from_contacts([contact_vectors(first), contact_vectors(second)], 4)
    if any(value != zzero() for value in linear_sum):
        raise ValueError("synthetic linear cancellation did not occur")
    if all(value == 0 for row in moments for value in row):
        raise ValueError("synthetic paired moment cancelled with its linear sum")
    q = [(Q(1), Q(0)), zzero()]
    difference = q + [zzero()]
    passive, _, _ = passive_step(q, [(difference, zzero(), [Q(0)] * 6)])
    return {
        "paired_moment_survives_linear_cancellation": True,
        "passive_norm_balance": passive["weighted_norm_balance"],
        "realification": passive["realification_verified"],
    }


def actual_observation(
    report: dict, limit: int, native_report: dict | None = None
) -> dict:
    if report.get("profile") != "matched-unit-octet-excitation-native-field":
        raise ValueError("the observer requires the matched unit native field report")
    lineages = report.get("body", {}).get("lineage", [])
    if not lineages:
        raise ValueError("the report has no field lineages")
    limit = min(limit, len(lineages))
    zero = [(Q(0), Q(0)) for _ in lineages[0]["incoming"]]
    previous = zero
    q_fields: list[list[Complex]] = []
    arrivals: list[list[Complex]] = []
    for lineage in lineages[:limit]:
        incoming = [phase(value) for value in lineage["incoming"]]
        q_fields.append([value for pair in zip(previous, incoming) for value in pair])
        arrivals.append(incoming)
        previous = incoming
    contacts: list[tuple[list[Complex], Complex, list[Q]]] = []
    prefix = [Q(0) for _ in range(len(q_fields[0] + arrivals[0]) * 2)]
    steps = []
    native_by_occurrence = {}
    if native_report is not None:
        if native_report.get("profile") != "matched-unit-octet-field-with-paired-junction":
            raise ValueError("the comparison requires the paired-junction native report")
        native_history = native_report.get("body", {}).get("junction_history", [])
        native_by_occurrence = {entry[0]: entry[1] for entry in native_history}
    for occurrence, (lineage, q_now, arrived) in enumerate(
        zip(lineages[:limit], q_fields, arrivals)
    ):
        source = lineage.get("received_from")
        if source is not None:
            if source >= occurrence:
                raise ValueError("source handle points to the future")
            source_q = q_fields[source]
            difference = source_q + [zscale(value, Q(-1)) for value in arrived]
            contacts.append((difference, zzero(), prefix[:]))
        step, contacts, v = passive_step(q_now, contacts, observe_full_matrix=occurrence < 12)
        next_prefix = add_vectors(prefix, scale_vector(v, Q(-1 if occurrence % 2 else 1)))
        for difference, internal, birth_prefix in contacts:
            birth_value = zsum(
                [
                    zmul(zconj(left), right)
                    for left, right in zip(difference, complexify(sub_vectors(next_prefix, birth_prefix)))
                ]
            )
            expected = zscale(birth_value, Q(-1 if occurrence % 2 else 1))
            if internal != expected:
                raise ValueError("alternating prefix decoder disagrees with internal current")
        step["alternating_decoder_verified"] = True
        prefix = next_prefix
        step.update({
            "occurrence": occurrence,
            "received_from": source,
            "contacts_after_birth": len(contacts),
            "reduced_i64_fits": all(
                step[key] <= 63
                for key in (
                    "reduced_v_numerator_bits",
                    "reduced_v_denominator_bits",
                    "reduced_outgoing_numerator_bits",
                    "reduced_outgoing_denominator_bits",
                )
            ),
            "woodbury_common_denominator_i64_fits": (
                step["bareiss"].get("system_common_denominator_bits", 0) <= 63
            ),
        })
        if step["full_matrix_bareiss"] is not None:
            step["full_matrix_common_denominator_i64_fits"] = (
                step["full_matrix_bareiss"]["rhs_denominator_bits"] <= 63
            )
            step["full_matrix_predivision_i128_fits"] = (
                step["full_matrix_bareiss"]["max_predivision_bits"] <= 127
            )
            step["full_matrix_adjugate_backsub_i128_fits"] = max(
                step["full_matrix_bareiss"]["max_adjugate_backsub_product_bits"],
                step["full_matrix_bareiss"]["max_adjugate_backsub_subtraction_bits"],
            ) <= 127
        if occurrence in native_by_occurrence:
            section = native_by_occurrence[occurrence]
            native_v = decode_native_segment(section, 0, len(v))
            native_outgoing = decode_native_segment(section, 1, len(v))
            native_h = decode_native_segment(section, 2, len(v))
            native_prefix = decode_native_segment(section, 3, len(v))
            exact_h = condensed_h(contacts) if contacts else [Q(0) for _ in v]
            exact_outgoing = sub_vectors(v, realify(q_now) + [Q(0) for _ in q_now])
            step["native_readback_comparison"] = {
                "potential_equal": native_v == v,
                "outgoing_equal": native_outgoing == exact_outgoing,
                "held_equal": native_h == exact_h,
                "prefix_equal": native_prefix == prefix,
                "all_equal": (
                    native_v == v
                    and native_outgoing == exact_outgoing
                    and native_h == exact_h
                    and native_prefix == prefix
                ),
            }
        steps.append(step)
    max_intermediate = max(
        (step["bareiss"].get("max_intermediate_bits", 0) for step in steps), default=0
    )
    max_reduced_num = max(
        (max(step["reduced_v_numerator_bits"], step["reduced_outgoing_numerator_bits"]) for step in steps),
        default=0,
    )
    max_reduced_den = max(
        (max(step["reduced_v_denominator_bits"], step["reduced_outgoing_denominator_bits"]) for step in steps),
        default=0,
    )
    full_steps = [step for step in steps if step["full_matrix_bareiss"] is not None]

    def first_failure(key: str) -> int | None:
        failure = next((step["occurrence"] for step in steps if not step[key]), None)
        return failure

    first_reduced_numerator_i64_failure = next(
        (
            step["occurrence"]
            for step in steps
            if max(step["reduced_v_numerator_bits"], step["reduced_outgoing_numerator_bits"]) > 63
        ),
        None,
    )
    first_reduced_denominator_i64_failure = next(
        (
            step["occurrence"]
            for step in steps
            if max(step["reduced_v_denominator_bits"], step["reduced_outgoing_denominator_bits"]) > 63
        ),
        None,
    )

    def first_full_failure(key: str) -> int | None:
        failure = next(
            (step["occurrence"] for step in full_steps if not step.get(key, True)), None
        )
        return failure

    return {
        "truth_status": "established-bounded",
        "evidence_tags": ["computational-witness"],
        "scope": f"exact passive reference over the first {limit} recorded native field occurrences",
        "native_model_or_update_executed": False,
        "occurrences": limit,
        "linked_occurrences": sum(step["received_from"] is not None for step in steps),
        "source_dimension_complex": len(q_fields[0]),
        "difference_dimension_complex": len(q_fields[0]) + len(arrivals[0]),
        "realified_dimension": len(q_fields[0] + arrivals[0]) * 2,
        "steps": steps,
        "maximum_reduced_numerator_bits": max_reduced_num,
        "maximum_reduced_denominator_bits": max_reduced_den,
        "maximum_bareiss_intermediate_bits": max_intermediate,
        "i128_signed_magnitude_bits": 127,
        "fits_i128_woodbury_predivision_aperture": all(
            step["bareiss"].get("max_predivision_bits", 0) <= 127 for step in steps
        ),
        "full_matrix_observation_limit": min(12, limit),
        "full_matrix_observed_occurrences": len(full_steps),
        "maximum_full_matrix_predivision_bits": max(
            (step["full_matrix_bareiss"]["max_predivision_bits"] for step in full_steps),
            default=0,
        ),
        "maximum_full_matrix_adjugate_equivalent_numerator_bits": max(
            (
                step["full_matrix_bareiss"]["adjugate_equivalent_numerator_bits"]
                for step in full_steps
            ),
            default=0,
        ),
        "maximum_full_matrix_adjugate_backsub_product_bits": max(
            (
                step["full_matrix_bareiss"]["max_adjugate_backsub_product_bits"]
                for step in full_steps
            ),
            default=0,
        ),
        "maximum_full_matrix_adjugate_backsub_subtraction_bits": max(
            (
                step["full_matrix_bareiss"]["max_adjugate_backsub_subtraction_bits"]
                for step in full_steps
            ),
            default=0,
        ),
        "first_reduced_i64_failure": first_failure("reduced_i64_fits"),
        "first_reduced_numerator_i64_failure": first_reduced_numerator_i64_failure,
        "first_reduced_denominator_i64_failure": first_reduced_denominator_i64_failure,
        "first_woodbury_common_denominator_i64_failure": first_failure(
            "woodbury_common_denominator_i64_fits"
        ),
        "first_full_matrix_rhs_denominator_i64_failure": first_full_failure(
            "full_matrix_common_denominator_i64_fits"
        ),
        "first_full_matrix_predivision_i128_failure": first_full_failure(
            "full_matrix_predivision_i128_fits"
        ),
        "first_full_matrix_adjugate_backsub_i128_failure": first_full_failure(
            "full_matrix_adjugate_backsub_i128_fits"
        ),
        "native_readback_comparison": (
            {
                "truth_status": "established-bounded",
                "evidence_tags": ["computational-witness", "measured"],
                "compared_occurrences": sum(
                    "native_readback_comparison" in step for step in steps
                ),
                "native_report_occurrences": len(native_by_occurrence),
                "all_equal": all(
                    step["native_readback_comparison"]["all_equal"]
                    for step in steps
                    if "native_readback_comparison" in step
                ),
            }
            if native_report is not None
            else None
        ),
        "separating_context_is_operated": False,
        "open_boundary": "The observer uses recorded source-handle indices and does not itself make historical context operative in native conduct.",
    }


def decode_native_segment(section: dict, segment: int, dimension: int) -> list[Q]:
    """Decode one private paired-junction report segment to adjacent real/imaginary rationals."""
    stride = dimension + 1
    intervals = section["intervals"]
    if section.get("rows") != 1 or section.get("width") != 4 * stride:
        raise ValueError("native paired report has an unexpected shape")
    at = segment * stride
    denominator = intervals[at + dimension][0]
    if denominator <= 0:
        raise ValueError("native paired report has a non-positive denominator")
    values: list[Q] = []
    for index in range(dimension):
        lower, upper = intervals[at + index]
        if lower != upper:
            raise ValueError("native paired report is not an exact point")
        values.append(Q(lower, denominator))
    return values


def write_new(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    with os.fdopen(descriptor, "w", encoding="utf-8") as output:
        json.dump(value, output, indent=2)
        output.write("\n")


def main() -> None:
    arguments = sys.argv[1:]
    if not arguments:
        raise SystemExit(
            "usage: inspect.py REPORT --output NEW.json [--occurrences N] [--native-report REPORT]"
        )
    report_path = Path(arguments.pop(0))
    output_path: Path | None = None
    native_report_path: Path | None = None
    occurrences = 25
    while arguments:
        option = arguments.pop(0)
        if option == "--output" and arguments:
            output_path = Path(arguments.pop(0))
        elif option == "--occurrences" and arguments:
            occurrences = int(arguments.pop(0))
        elif option == "--native-report" and arguments:
            native_report_path = Path(arguments.pop(0))
        else:
            raise SystemExit(f"unknown or incomplete option: {option}")
    if output_path is None:
        raise SystemExit("--output is required")
    if occurrences <= 0:
        raise SystemExit("--occurrences must be positive")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    native_report = (
        json.loads(native_report_path.read_text(encoding="utf-8"))
        if native_report_path is not None
        else None
    )
    result = {
        "schema": "holonics.alpha-passive-junction-observer.v1",
        "profile": "exact-coupled-passive-junction-reference",
        "synthetic": synthetic_checks(),
        "actual": actual_observation(report, occurrences, native_report),
    }
    write_new(output_path, result)
    actual = result["actual"]
    print(json.dumps({
        "schema": result["schema"],
        "occurrences": actual["occurrences"],
        "linked_occurrences": actual["linked_occurrences"],
        "maximum_reduced_numerator_bits": actual["maximum_reduced_numerator_bits"],
        "maximum_reduced_denominator_bits": actual["maximum_reduced_denominator_bits"],
        "maximum_woodbury_predivision_bits": max(
            step["bareiss"].get("max_predivision_bits", 0) for step in actual["steps"]
        ),
        "maximum_full_matrix_predivision_bits": actual[
            "maximum_full_matrix_predivision_bits"
        ],
        "first_reduced_i64_failure": actual["first_reduced_i64_failure"],
        "first_reduced_denominator_i64_failure": actual[
            "first_reduced_denominator_i64_failure"
        ],
        "first_woodbury_common_denominator_i64_failure": actual[
            "first_woodbury_common_denominator_i64_failure"
        ],
        "first_full_matrix_predivision_i128_failure": actual[
            "first_full_matrix_predivision_i128_failure"
        ],
        "fits_i128_woodbury_predivision_aperture": actual[
            "fits_i128_woodbury_predivision_aperture"
        ],
        "native_model_or_update_executed": False,
    }))


if __name__ == "__main__":
    main()
