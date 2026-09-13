#!/usr/bin/env python3
"""Run exact C5 and C5xC5 actions through the public HNN math session.

The matrices are supplied mathematical data and the monic recurrence coefficients are
consumed from the existing exact inference receipt.  The script independently constructs
powers, recurrence reductions, and input products so the native JSONL return is checked
against exact mathematics.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


def rat(value: int) -> dict[str, str]:
    return {"numerator": str(value), "denominator": "1"}


def matrix_wire(matrix: list[list[int]]) -> list[list[dict[str, str]]]:
    return [[rat(value) for value in row] for row in matrix]


def matrix_mul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def matrix_add(a: list[list[int]], b: list[list[int]], scale: int = 1) -> list[list[int]]:
    return [[x + scale * y for x, y in zip(row_a, row_b)] for row_a, row_b in zip(a, b)]


def matrix_scale(a: list[list[int]], scale: int) -> list[list[int]]:
    return [[scale * value for value in row] for row in a]


def zero_matrix(n: int) -> list[list[int]]:
    return [[0 for _ in range(n)] for _ in range(n)]


def identity(n: int) -> list[list[int]]:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def shift(n: int) -> list[list[int]]:
    return [[int(j == (i + 1) % n) for j in range(n)] for i in range(n)]


def transpose(a: list[list[int]]) -> list[list[int]]:
    return [list(row) for row in zip(*a)]


def kron(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    result = []
    for row_a in a:
        for row_b in b:
            result.append([x * y for x in row_a for y in row_b])
    return result


def vector_apply(a: list[list[int]], x: list[int]) -> list[int]:
    return [sum(v * y for v, y in zip(row, x)) for row in a]


def power(a: list[list[int]], n: int) -> list[list[int]]:
    result = identity(len(a))
    base = a
    while n:
        if n & 1:
            result = matrix_mul(result, base)
        base = matrix_mul(base, base)
        n >>= 1
    return result


def reduced_power(a: list[list[int]], n: int, coefficients: list[int]) -> list[list[int]]:
    """Reduce x^n modulo a supplied monic polynomial, then evaluate at a."""
    degree = len(coefficients) - 1
    if coefficients[-1] != 1:
        raise ValueError("polynomial must be monic")
    remainder = [0] * max(degree, n + 1)
    remainder[n] = 1
    for k in range(n, degree - 1, -1):
        lead = remainder[k]
        if lead:
            for j, coefficient in enumerate(coefficients):
                remainder[k - degree + j] -= lead * coefficient
    powers = [identity(len(a))]
    for _ in range(1, degree):
        powers.append(matrix_mul(powers[-1], a))
    result = [[0 for _ in a] for _ in a]
    for coefficient, term in zip(remainder, powers):
        result = matrix_add(result, term, coefficient)
    return result


def polynomial_matrix(a: list[list[int]], coefficients: list[int]) -> list[list[int]]:
    result = zero_matrix(len(a))
    for exponent, coefficient in enumerate(coefficients):
        result = matrix_add(result, power(a, exponent), coefficient)
    return result


def request(operation: str, **body: object) -> dict[str, object]:
    payload = {"operation": operation, **body}
    return {
        "schema": "org.holonics.hna.stream-request.v1",
        "command": {"action": "mathematical-request", "request": payload},
    }


def apply_request(operator: int, values: list[int], retain: bool = False) -> dict[str, object]:
    return request(
        "apply",
        operator=operator,
        left=[rat(v) for v in values],
        retain_product=retain,
    )


def output_values(event: dict[str, object]) -> list[int]:
    values = event["value"]["output"]  # type: ignore[index]
    result = []
    for value in values:  # type: ignore[union-attr]
        numerator = int(value["numerator"])
        denominator = int(value["denominator"])
        if numerator % denominator:
            raise AssertionError((numerator, denominator))
        result.append(numerator // denominator)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, default=Path("target/debug/holonics"))
    parser.add_argument("--directory", type=Path, default=Path(__file__).parent)
    parser.add_argument(
        "--inference-receipt",
        type=Path,
        default=Path(".local/artifacts/2026-09-12-geometry/phase_clock_smith.json"),
    )
    parser.add_argument(
        "--reuse-output",
        action="store_true",
        help="rebuild concise result metadata from the existing stdout without rerunning native work",
    )
    args = parser.parse_args()
    directory: Path = args.directory
    directory.mkdir(parents=True, exist_ok=True)

    try:
        inference = json.loads(args.inference_receipt.read_text())
    except FileNotFoundError as error:
        raise SystemExit(
            f"missing inference receipt {args.inference_receipt}: run torus_smith_sources "
            "to produce phase_clock_smith.json; no supplied-coefficient fallback is used"
        ) from error
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"invalid inference receipt {args.inference_receipt}: {error}") from error
    if inference.get("schema") != "holonic-engine.phase-clock-smith.v1":
        raise SystemExit(
            f"invalid inference receipt {args.inference_receipt}: expected "
            "holonic-engine.phase-clock-smith.v1"
        )
    inferred_by_name = {row.get("name"): row for row in inference.get("recurrences", [])}
    try:
        l_inference = inferred_by_name["C5-Laplacian"]
        k_inference = inferred_by_name["C5xC5-Kronecker-sum-Laplacian"]
        l_poly = [int(value) for value in l_inference["monic_coefficients"]]
        k_poly = [int(value) for value in k_inference["monic_coefficients"]]
        if l_poly[-1] != 1 or k_poly[-1] != 1:
            raise ValueError("inferred recurrence is not monic")
    except (KeyError, TypeError, ValueError) as error:
        raise SystemExit(
            f"inference receipt {args.inference_receipt} lacks monic C5/C5xC5 recurrence "
            f"coefficients: {error}"
        ) from error

    p = shift(5)
    l5 = matrix_add(
        matrix_scale(identity(5), 2), matrix_add(p, transpose(p)), scale=-1
    )
    # The canonical polynomial is retained for an independent check; the recurrence source used
    # below comes from the existing exact inference receipt loaded above.
    canonical_l_poly = [0, 5, -5, 1]
    assert l_poly == canonical_l_poly
    l16 = reduced_power(l5, 16, l_poly)
    assert polynomial_matrix(l5, l_poly) == zero_matrix(5)
    assert l16 == power(l5, 16)
    x5 = [2, -1, 3, 5, -4]

    k = matrix_add(kron(l5, identity(5)), kron(identity(5), l5))
    # The canonical factored polynomial is retained for an independent check; inferred coefficients
    # are the recurrence source used below.
    canonical_k_poly = [0, -500, 850, -525, 150, -20, 1]
    assert k_poly == canonical_k_poly
    # Coefficients are ascending; expand the canonical factors independently as a check.
    factor = [[0, 1], [-5, 1], [5, -5, 1], [20, -10, 1]]
    expanded = [1]
    for f in factor:
        next_coefficients = [0] * (len(expanded) + len(f) - 1)
        for i, x in enumerate(expanded):
            for j, y in enumerate(f):
                next_coefficients[i + j] += x * y
        expanded = next_coefficients
    assert expanded == canonical_k_poly, expanded
    k12 = reduced_power(k, 12, k_poly)
    assert polynomial_matrix(k, k_poly) == zero_matrix(25)
    assert k12 == power(k, 12)
    x25 = [((7 * i * i + 3 * i + 1) % 11) - 5 for i in range(25)]

    requests: list[dict[str, object]] = []
    # L, L^2 and L^3 are all formed through public resident composition.
    requests.append(request("construct-linear", coefficients=matrix_wire(l5)))
    requests.append(request("compose", operator=0, following=0))
    requests.append(request("compose", operator=1, following=0))
    requests.append(apply_request(2, x5, retain=True))
    requests.append(request("read-product", operator=2, product=0))
    # A recurrence-reduced L^16 action is supplied as a new exact operator and consumed natively.
    requests.append(request("construct-linear", coefficients=matrix_wire(l16)))
    requests.append(apply_request(3, x5))

    # Construct the full K powers as supplied exact matrices. The public Compose path is intended
    # for compatible retained product cores; it is not needed to expand this singular operator.
    requests.append(request("construct-linear", coefficients=matrix_wire(k)))
    for exponent in range(2, 7):
        requests.append(request("construct-linear", coefficients=matrix_wire(power(k, exponent))))
    # Operators 5..9 are supplied exact K^2..K^6; include K itself.
    for operator in range(4, 10):
        requests.append(apply_request(operator, x25, retain=(operator == 9)))
    requests.append(request("read-product", operator=9, product=1))
    requests.append(request("construct-linear", coefficients=matrix_wire(k12)))
    requests.append(apply_request(10, x25))
    # A later complex analyzer separates two inputs with the same separate intensity face.
    analyzer = [[1, 0, 0, -1], [0, 1, 1, 0], [1, 0, 0, 1], [0, 1, -1, 0]]
    phase_plus = [2, 0, 0, 1]
    phase_minus = [2, 0, 0, -1]
    requests.append(request("construct-linear", coefficients=matrix_wire(analyzer)))
    requests.append(apply_request(11, phase_plus))
    requests.append(apply_request(11, phase_minus))

    input_path = directory / "public-mathematical-session.jsonl"
    output_path = directory / "public-mathematical-session.stdout.jsonl"
    receipt_path = directory / "public-mathematical-session.receipt.json"
    input_path.write_text("\n".join(json.dumps(item, separators=(",", ":")) for item in requests) + "\n")
    if args.reuse_output:
        if not output_path.exists() or not receipt_path.exists():
            raise SystemExit(f"cannot reuse missing native evidence under {directory}")
    else:
        completed = subprocess.run(
            [str(args.binary), "hna", "mathematical-session", "--input", str(input_path)],
            check=False,
            capture_output=True,
            text=True,
        )
        output_path.write_text(completed.stdout)
        receipt_lines = [line for line in completed.stderr.splitlines() if line.strip()]
        if receipt_lines:
            receipt_path.write_text(receipt_lines[-1] + "\n")
        if completed.returncode:
            raise SystemExit(f"public mathematical session failed: {completed.stderr}")
    events = [json.loads(line) for line in output_path.read_text().splitlines() if line.strip()]
    returns = [event for event in events if event.get("event") == "mathematical-return"]
    applied = [event for event in returns if event["value"].get("status") == "applied"]
    reads = [event for event in returns if event["value"].get("status") == "read"]
    # Applied order: L^3, reduced L^16, K, K^2, ..., K^6, reduced K^12.
    l1x = vector_apply(l5, x5)
    l2x = vector_apply(power(l5, 2), x5)
    assert output_values(applied[0]) == vector_apply(power(l5, 3), x5)
    assert output_values(applied[0]) == [5 * l2x[i] - 5 * l1x[i] for i in range(5)]
    assert output_values(reads[0]) == vector_apply(power(l5, 3), x5)
    assert output_values(applied[1]) == vector_apply(l16, x5)
    k6 = power(k, 6)
    # Evaluate the supplied polynomial on the vector from the six native powers.
    native_k_powers = [output_values(applied[index]) for index in range(2, 8)]
    k0x = x25
    k1x, k2x, k3x, k4x, k5x, k6xv = native_k_powers
    annihilated = [
        k6xv[i] - 15 * k5x[i] + 205 * k4x[i] - 80 * k3x[i] + 15 * k2x[i] - 0 * k1x[i]
        for i in range(25)
    ]
    # Correct expansion has coefficients [0,-500,850,-525,150,-20,1].
    annihilated = [-500 * k1x[i] + 850 * k2x[i] - 525 * k3x[i] + 150 * k4x[i] - 20 * k5x[i] + k6xv[i] for i in range(25)]
    assert annihilated == [0] * 25, annihilated
    assert output_values(reads[1]) == vector_apply(k6, x25)
    assert output_values(applied[8]) == vector_apply(k12, x25)
    assert output_values(applied[9]) == vector_apply(analyzer, phase_plus) == [1, 0, 3, 0]
    assert output_values(applied[10]) == vector_apply(analyzer, phase_minus) == [3, 0, 1, 0]
    plus_power = [value * value for value in output_values(applied[9])]
    minus_power = [value * value for value in output_values(applied[10])]
    assert plus_power[:2] == [1, 0] and minus_power[:2] == [9, 0]
    metadata = {
        "scope": "public HNN mathematical-session exact resident matrix actions",
        "supplied": {
            "L5": l5,
            "canonical_L5_minimal_polynomial_ascending": canonical_l_poly,
            "K25": k,
            "canonical_K25_minimal_polynomial_ascending": canonical_k_poly,
            "vectors": {"x5": x5, "x25": x25},
            "phase_analyzer": analyzer,
            "phase_inputs": {"plus": phase_plus, "minus": phase_minus},
        },
        "inferred_or_checked": {
            "inference_receipt": str(args.inference_receipt),
            "inference_summary": {
                "C5-Laplacian": {
                    "first_consistent_degree": l_inference["first_consistent_degree"],
                    "monic_coefficients": l_inference["monic_coefficients"],
                    "coefficient_kernel": l_inference.get("coefficient_kernel", []),
                    "power_construction_work": l_inference.get("power_construction_work"),
                },
                "C5xC5-Kronecker-sum-Laplacian": {
                    "first_consistent_degree": k_inference["first_consistent_degree"],
                    "monic_coefficients": k_inference["monic_coefficients"],
                    "coefficient_kernel": k_inference.get("coefficient_kernel", []),
                    "power_construction_work": k_inference.get("power_construction_work"),
                },
            },
            "inferred_L5_recurrence_coefficients_ascending": l_poly,
            "inferred_K25_recurrence_coefficients_ascending": k_poly,
            "native_L3_equals_5L2_minus_5L": True,
            "native_K6_annihilated_by_supplied_polynomial": True,
            "reduced_powers": {
                "L16": {"dimension": 5, "same_as_direct_power": True, "max_abs_entry": max(abs(v) for row in l16 for v in row)},
                "K12": {"dimension": 25, "same_as_direct_power": True, "max_abs_entry": max(abs(v) for row in k12 for v in row)},
            },
            "phase_separator_outputs": {
                "plus": [1, 0, 3, 0], "minus": [3, 0, 1, 0],
                "normalized_powers": {"plus": ["1/10", "9/10"], "minus": ["9/10", "1/10"]},
            },
        },
        "requests": len(requests),
        "events": len(events),
        "return_count": len(returns),
        "native_operator_chain": {"L": [0, 1, 2], "L16_reduced": 3, "K": [4, 5, 6, 7, 8, 9], "K12_reduced": 10, "phase_analyzer": 11},
        "composition_scope": "L3 was formed through public Compose; K2..K6 and reduced K12 were supplied as exact matrices because this session's Compose contract is a retained-core composition path, not a polynomial combiner",
        "cost_scope": "per-request cost objects are retained in stdout; process startup/JSON transport are excluded by the native request cost field",
    }
    (directory / "result.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
