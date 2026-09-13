"""Public resident matrix action for the oriented split passage; no candidate ranking."""
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]


def wire(value):
    value = Q(value)
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def request(**body):
    return {"schema": "org.holonics.hna.stream-request.v1",
            "command": {"action": "mathematical-request", "request": body}}


def multiply(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(2)), Q(0))
             for j in range(2)] for i in range(2)]


def power(a, n):
    result = [[Q(1), Q(0)], [Q(0), Q(1)]]
    for _ in range(n):  # Independent observer check of the compiled native power.
        result = multiply(a, result)
    return result


def main():
    total, step = Q(2), Q(1, 4)
    matrix = [[Q(1), step * total], [step, Q(1)]]
    requests = [request(operation="construct-linear", coefficients=[[wire(x) for x in row] for row in matrix])]
    apertures = [1, 4, 16]
    query_rows = []
    for operator, count in enumerate(apertures, start=1):
        requests.append(request(operation="power", operator=0, exponent=count))
        for origin in [Q(1), Q(3)]:
            query_rows.append((len(requests), count, origin))
            requests.append(request(operation="apply", operator=operator,
                                    left=[wire(origin), wire(1)], retain_product=False))
    completed = subprocess.run(
        [str(ROOT / "target/debug/holonics"), "hna", "mathematical-session", "--input", "-"],
        input="".join(json.dumps(row) + "\n" for row in requests),
        capture_output=True, text=True, check=True)
    events = [json.loads(line) for line in completed.stdout.splitlines() if line.strip()]
    assert len(events) == len(requests)
    for event in events:
        assert event.get("event") == "mathematical-return", event
    observations = []
    for index, count, origin in query_rows:
        response = events[index]["value"]
        assert response["status"] == "applied"
        homogeneous = [Q(int(x["numerator"]), int(x["denominator"])) for x in response["output"]]
        expected_matrix = power(matrix, count)
        expected = [row[0] * origin + row[1] for row in expected_matrix]
        assert homogeneous == expected
        numerator, denominator = homogeneous
        assert denominator > 0
        coordinate = numerator / denominator
        a, b = expected_matrix[0]
        c, d = expected_matrix[1]
        determinant = a * d - b * c
        undivided_residual = numerator**2 - total * denominator**2
        assert undivided_residual == determinant * (origin**2 - total)
        recovered = (d * numerator - b * denominator) / (-c * numerator + a * denominator)
        assert recovered == origin
        before_residual, after_residual = origin**2 - total, coordinate**2 - total
        assert before_residual * after_residual > 0
        before_work, after_work = origin + total / origin, coordinate + total / coordinate
        assert after_work < before_work
        observations.append({"steps": count, "origin": wire(origin),
                             "homogeneous_return": [wire(x) for x in homogeneous],
                             "coordinate_face": wire(coordinate),
                             "oriented_step": wire(coordinate - origin),
                             "signed_residual_before": wire(before_residual),
                             "signed_residual_after": wire(after_residual),
                             "work_before": wire(before_work), "work_after": wire(after_work),
                             "matrix_determinant": wire(determinant),
                             "undivided_signed_residual": wire(undivided_residual),
                             "recovered_source": wire(recovered)})
    result = {"source": {"constraint": "x*y=T", "T": wire(total), "step": wire(step),
                         "matrix": [[wire(x) for x in row] for row in matrix]},
              "observations": observations, "native_returns": events,
              "process_receipt": json.loads(completed.stderr.strip().splitlines()[-1]),
              "scope": "declared split relation; existing fixed-linear power construction and resident application; source signs and undivided pair retained; exterior exact ratio decoder/reference checks; no city/chess solver or rule-acquisition claim"}
    (Path(__file__).parent / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"verified_returns": len(observations), "steps": apertures,
                      "source_reconstruction": True, "signed_residuals_retained": True}))


if __name__ == "__main__":
    main()
