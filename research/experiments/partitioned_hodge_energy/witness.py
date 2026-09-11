"""Exact exterior four-edge cycle: Hodge pieces, sharp cuts and implicit diffusion.

Energy is the declared quadratic norm (no joule calibration). The local time is
the step parameter of (I + tau L) j_new = j_old, not the RH heat clock.
"""
from fractions import Fraction as Q
import argparse
import json
from pathlib import Path


def add(x, y):
    return [a + b for a, b in zip(x, y)]


def scale(a, x):
    return [a * b for b in x]


def norm2(x):
    return sum((a * a for a in x), Q(0))


def laplacian(x):
    n = len(x)
    return [2 * x[i] - x[(i - 1) % n] - x[(i + 1) % n] for i in range(n)]


def boundary(x):
    return [x[(i - 1) % len(x)] - x[i] for i in range(len(x))]


def restrict(x, indices):
    return [a if i in indices else Q(0) for i, a in enumerate(x)]


def stringify(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, list):
        return [stringify(x) for x in value]
    if isinstance(value, dict):
        return {k: stringify(v) for k, v in value.items()}
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source = list(map(Q, (1, 2, 3, 4)))
    harmonic = [sum(source) / len(source)] * len(source)
    potential = [Q(0), Q(-3, 2), Q(-2), Q(-3, 2)]
    exact = [potential[(i + 1) % 4] - potential[i] for i in range(4)]
    assert source == add(harmonic, exact)
    assert boundary(harmonic) == [0] * 4
    assert sum(a * b for a, b in zip(harmonic, exact)) == 0
    # Actual eigenvectors of this cycle's incidence Laplacian.
    mode2, mode4 = list(map(Q, (-1, -1, 1, 1))), [Q(-1, 2), Q(1, 2)] * 2
    assert exact == add(mode2, mode4)
    assert laplacian(mode2) == scale(2, mode2)
    assert laplacian(mode4) == scale(4, mode4)
    pieces = ([0, 1], [2, 3])
    cut_boundaries = [boundary(restrict(harmonic, p)) for p in pieces]
    assert add(*cut_boundaries) == [0] * 4
    rows = []
    for tau in (Q(0), Q(1, 8), Q(1, 2), Q(1)):
        remainder = add(scale(1 / (1 + 2 * tau), mode2),
                        scale(1 / (1 + 4 * tau), mode4))
        current = add(harmonic, remainder)
        lj = laplacian(current)
        assert add(current, scale(tau, lj)) == source
        dissipation = sum(a * b for a, b in zip(current, lj))
        balance = 2 * tau * dissipation + tau * tau * norm2(lj)
        assert norm2(source) - norm2(current) == balance >= 0
        local = []
        for part in pieces:
            h, e, j = (restrict(x, part) for x in (harmonic, remainder, current))
            mixed = 2 * sum(a * b for a, b in zip(h, e))
            assert norm2(j) == norm2(h) + norm2(e) + mixed
            local.append({"edges": part, "energy": norm2(j),
                          "harmonic_energy": norm2(h), "exact_energy": norm2(e),
                          "mixed_contribution": mixed})
        assert sum(p["mixed_contribution"] for p in local) == 0
        rows.append({"tau": tau, "current": current, "retained_harmonic": harmonic,
                     "exact_part": remainder, "energy": norm2(current),
                     "energy_decrease": balance, "pieces": local})
    # Two different operators on the same four product coordinates. Their small
    # positive faces differ, but so do their null fibres.
    a = Q(1, 8)
    modes = (Q(0), a)
    independent = [x + y for x in modes for y in modes]
    product = [x * y for x in modes for y in modes]
    assert independent.count(0) == 1 and product.count(0) == 3
    assert min(x for x in independent if x > 0) == a
    assert min(x for x in product if x > 0) == a * a
    result = stringify({"scope": "exact finite cycle and declared implicit-step law",
                        "source": source, "potential": potential,
                        "harmonic_cut_boundaries": cut_boundaries, "steps": rows,
                        "paired_mode_control": {"individual": list(modes),
                            "independent_sum": independent, "tensor_product": product,
                            "independent_kernel_dimension": 1,
                            "product_kernel_dimension": 3,
                            "scope": "distinct diagonal operators; not an RH threshold inference"}})
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    for row in result["steps"]:
        print(json.dumps({"tau": row["tau"], "current": row["current"],
                          "energy": row["energy"], "pieces": row["pieces"]}))


if __name__ == "__main__":
    main()
