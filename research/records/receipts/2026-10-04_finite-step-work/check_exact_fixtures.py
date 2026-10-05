"""Exact, reproducible algebraic witnesses outside HNN; no compiler or training."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import resource
import time

HERE = Path(__file__).resolve().parent


def matrix(rows):
    return [[F(v) for v in row] for row in rows]


def vector(values):
    return [F(v) for v in values]


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def apply(a, x):
    return [sum((v * w for v, w in zip(row, x)), F(0)) for row in a]


def subtract(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[c * v for v in row] for row in a]


def plus(x, y):
    return [a + b for a, b in zip(x, y)]


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), F(0))


def quadratic(g, x):
    return dot(x, apply(g, x))


def inverse(a):
    if len(a) == 1:
        assert a[0][0]
        return [[1 / a[0][0]]]
    p, q = a[0]
    r, s = a[1]
    determinant = p * s - q * r
    assert determinant
    return [[s / determinant, -q / determinant],
            [-r / determinant, p / determinant]]


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, list):
        return [encode(v) for v in value]
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    return value


def check_affine(case):
    t, g0, g1 = (matrix(case[k]) for k in ["T", "G0", "G1"])
    x, b = vector(case["x"]), vector(case["b"])
    assert transpose(g1) == g1
    reached = plus(apply(t, x), b)
    form = subtract(multiply(multiply(transpose(t), g1), t), g0)
    homogeneous = quadratic(form, x)
    cross = 2 * dot(x, apply(multiply(transpose(t), g1), b))
    source = quadratic(g1, b)
    work = (quadratic(g1, reached) - quadratic(g0, x)) / 2
    assert 2 * work == homogeneous + cross + source
    result = {"name": case["name"], "work": work,
              "homogeneous_work": homogeneous / 2,
              "cross_work": cross / 2, "source_work": source / 2}
    if "P0" in case:
        p0, p1 = matrix(case["P0"]), matrix(case["P1"])
        v0, v1 = inverse(p0), inverse(p1)
        th = multiply(multiply(p1, t), v0)
        bh, yh = apply(p1, b), apply(p0, x)
        g0h = multiply(multiply(transpose(v0), g0), v0)
        g1h = multiply(multiply(transpose(v1), g1), v1)
        formh = subtract(multiply(multiply(transpose(th), g1h), th), g0h)
        assert formh == multiply(multiply(transpose(v0), form), v0)
        reachedh = plus(apply(th, yh), bh)
        assert reachedh == apply(p1, reached)
        assert quadratic(g0h, yh) == quadratic(g0, x)
        assert quadratic(g1h, reachedh) == quadratic(g1, reached)
        assert quadratic(formh, yh) == homogeneous
        assert 2 * dot(yh, apply(multiply(transpose(th), g1h), bh)) == cross
        assert quadratic(g1h, bh) == source
        result.update(V0=v0, V1=v1, T_hat=th, G0_hat=g0h,
                      G1_hat=g1h, F=form, F_hat=formh)
        if "gain_form_r" in case:
            rate = F(case["gain_form_r"])
            bound = subtract(multiply(multiply(transpose(t), g1), t), scale(rate, g0))
            boundh = subtract(multiply(multiply(transpose(th), g1h), th), scale(rate, g0h))
            assert boundh == multiply(multiply(transpose(v0), bound), v0)
            result.update(gain_form_r=rate, gain_form=bound, gain_form_hat=boundh)
        if "expected_wrong_metric_work" in case:
            wrong = (quadratic(g1, reachedh) - quadratic(g0, x)) / 2
            assert wrong == F(case["expected_wrong_metric_work"])
            result["wrong_untransported_metric_work"] = wrong
    if "eta" in case:
        eta = vector(case["eta"])
        unresolved = dot(eta, apply(g1, reached)) + quadratic(g1, eta) / 2
        full = (quadratic(g1, plus(reached, eta)) - quadratic(g0, x)) / 2
        assert full == work + unresolved
        if "P0" in case:
            etah = apply(p1, eta)
            assert unresolved == dot(etah, apply(g1h, reachedh)) + quadratic(g1h, etah) / 2
        result.update(work=full, undivided_unresolved_work=2 * unresolved,
                      unresolved_work=unresolved)
    for key, expected in case.items():
        if key.startswith("expected_") and key != "expected_wrong_metric_work":
            assert result[key[len("expected_"):]] == F(expected), (case["name"], key)
    return result


started = time.perf_counter_ns()
fixtures_path = HERE / "exact-fixtures.json"
fixtures = json.loads(fixtures_path.read_text())
results = []
for case in fixtures["elementary"] + fixtures["non_diagonal"]:
    if case["name"] == "future_separator":
        g, t = matrix(case["G"]), matrix(case["T"])
        r, k = vector(case["receiver"]), vector(case["difference"])
        assert multiply(multiply(transpose(t), g), t) == g
        result = {"name": case["name"], "present": dot(r, k),
                  "future": dot(r, apply(t, k)),
                  "energy_change": (quadratic(g, apply(t, k)) - quadratic(g, k)) / 2}
        for key in ["present", "future", "energy_change"]:
            assert result[key] == F(case["expected_" + key])
    else:
        result = check_affine(case)
    results.append(result)

prior_path = HERE / "source-validation.json"
prior = json.loads(prior_path.read_text())
for before, after in zip(prior["exact_checks"][-2:], results[-2:]):
    assert before["name"] == after["name"]
    assert F(before["homogeneous"]) == 2 * after["homogeneous_work"]
    assert F(before["cross"]) == 2 * after["cross_work"]
    assert F(before["source"]) == 2 * after["source_work"]
    assert F(before["undivided_work"]) == 2 * (after["work"] - after["unresolved_work"])
    assert F(before["undivided_unresolved_work"]) == after["undivided_unresolved_work"]

receipt = {"status": "seven_reproducible_exact_checks_passed",
           "grade": "exact computational witnesses; not Lean verification",
           "method": fixtures["arithmetic"], "fixture_count": len(results),
           "fixtures_sha256": hashlib.sha256(fixtures_path.read_bytes()).hexdigest(),
           "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "prior_receipt_preserved_sha256": hashlib.sha256(prior_path.read_bytes()).hexdigest(),
           "prior_non_diagonal_readings_reproduced": True,
           "results": encode(results), "elapsed_ns": time.perf_counter_ns() - started,
           "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
           "compiler_invocations": 0, "training_runs": 0}
with (HERE / "exact-checks-02.json").open("x") as stream:
    json.dump(receipt, stream, indent=2)
    stream.write("\n")
print(json.dumps({k: receipt[k] for k in ["status", "fixture_count", "elapsed_ns",
                                         "peak_rss_kib", "prior_non_diagonal_readings_reproduced"]}))
