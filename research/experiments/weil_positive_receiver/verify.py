#!/usr/bin/env python3
"""Independent integer/rational checks of the saved Weil-square receipt."""

import json
from fractions import Fraction
from pathlib import Path


def decode(pair):
    return Fraction(pair["rational"]), Fraction(pair["sqrt2"])


def sign_root2(a, b):
    if a == 0:
        return (b > 0) - (b < 0)
    if b == 0 or (a > 0) == (b > 0):
        return (a > 0) - (a < 0)
    assert a * a != 2 * b * b
    dominant = a if a * a > 2 * b * b else b
    return (dominant > 0) - (dominant < 0)


def verify_case(row, c):
    assert row["relative_sign"] == c
    # Expand the source word (1+c T) and its reflected word (1+c T^-1).
    word = {0: 1, 1: c}
    expected_h = {}
    for k in (-2, -1, 0, 1, 2):
        expected_h[str(k)] = sum(
            ai * word.get(i - k, 0) for i, ai in word.items()
        )
    assert row["autocorrelation_at_k_log2"] == expected_h
    assert expected_h == {"-2": 0, "-1": c, "0": 2, "1": c, "2": 0}

    matrix = [[expected_h["0"], expected_h["-1"]],
              [expected_h["1"], expected_h["0"]]]
    assert row["address_gram"] == matrix
    determinant = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    assert row["address_gram_determinant"] == determinant == 3
    assert matrix[0][0] > 0

    # q(a,b) = (a+c*b)^2 + a^2 + b^2, audited coefficientwise.
    squares = row["positive_square_decomposition"]
    coefficients = [Fraction(0), Fraction(0), Fraction(0)]
    for term in squares:
        u, v = map(Fraction, term["linear_form"])
        w = Fraction(term["coefficient"])
        coefficients[0] += w * u * u
        coefficients[1] += 2 * w * u * v
        coefficients[2] += w * v * v
    assert coefficients == [matrix[0][0], 2 * matrix[0][1], matrix[1][1]]

    # e^-2L=1/4 and e^-L/2=sqrt(2)/2 exactly, with L=log(2).
    prime_a, prime_b = decode(row["prime_n2_coefficient_times_log2"])
    assert (prime_a, prime_b) == (0, Fraction(expected_h["1"] + expected_h["-1"], 2))
    assert row["prime_n2_sign"] == sign_root2(prime_a, prime_b)
    assert row["minus_prime_n2_sign"] == sign_root2(-prime_a, -prime_b)
    arch_a, arch_b = decode(row["archimedean_integrand_at_log2"])
    even_at_L = Fraction(expected_h["1"] + expected_h["-1"], 2)
    expected_arch_a = Fraction(expected_h["0"], 4) / Fraction(3, 4)
    expected_arch_b = (-even_at_L / 2) / Fraction(3, 4)
    assert (arch_a, arch_b) == (expected_arch_a, expected_arch_b)
    assert row["archimedean_integrand_sign"] == sign_root2(arch_a, arch_b)
    polar_a, polar_b = decode(row["polar_coefficient_times_B_squared"])
    assert (polar_a, polar_b) == (Fraction(4), Fraction(3 * c))
    assert row["polar_sign"] == sign_root2(polar_a, polar_b)


def verify_population(population, denominator):
    assert population["common_denominator"] == denominator
    rows = population["rows"]
    assert len(rows) == 2 * denominator + 1
    counts = {}
    for row, k in zip(rows, range(-denominator, denominator + 1)):
        c = Fraction(k, denominator)
        h0 = 1 + c * c
        assert row["numerator"] == k
        assert Fraction(row["relative_weight"]) == c
        determinant = h0 * h0 - c * c
        assert determinant == 1 + c * c + c**4 > 0
        assert Fraction(row["gram_determinant"]) == determinant
        expected_signs = {
            "prime": sign_root2(Fraction(0), c),
            "archimedean_at_log2": sign_root2(h0 / 3, -2 * c / 3),
            "polar": sign_root2(2 * h0, 3 * c),
        }
        assert row["signs"] == expected_signs
        label = "/".join(str(expected_signs[key]) for key in
                         ("prime", "archimedean_at_log2", "polar"))
        counts[label] = counts.get(label, 0) + 1
    assert population["sign_class_counts"] == counts

    # Exact floor bounds for irrational phase thresholds:
    # arch negative iff k/d > sqrt(2)-1;
    # polar negative iff -k/d > 1/sqrt(2).
    arch_floor = max(k for k in range(denominator + 1)
                     if (k + denominator)**2 < 2 * denominator**2)
    polar_floor = max(k for k in range(denominator + 1)
                      if 2 * k * k < denominator**2)
    assert counts.get("1/-1/1", 0) == denominator - arch_floor
    assert counts.get("-1/1/-1", 0) == denominator - polar_floor
    assert counts.get("-1/1/1", 0) == polar_floor
    assert counts.get("1/1/1", 0) == arch_floor
    assert counts.get("0/1/1", 0) == 1


def main():
    receipt = json.loads(Path(__file__).with_name("receipt.json").read_text())
    assert receipt["source"]["eps"] == "1/16"
    assert Fraction(2, 16) < Fraction(1, 2)
    assert Fraction(2, 16) < Fraction(1, 3)
    assert receipt["scope"]["prime_cutoff"] == "every N>=2; only n=2 contributes"
    assert receipt["scope"]["global_weil_positivity"] == "unresolved"
    cases = receipt["cases"]
    assert len(cases) == 2
    verify_case(cases[0], -1)
    verify_case(cases[1], 1)
    assert cases[0]["prime_n2_sign"] == -cases[1]["prime_n2_sign"]
    assert cases[0]["archimedean_integrand_sign"] == -cases[1]["archimedean_integrand_sign"]
    assert cases[0]["polar_sign"] == -cases[1]["polar_sign"]
    populations = receipt["phase_populations"]
    assert len(populations) == 2
    verify_population(populations[0], 8)
    verify_population(populations[1], 16)
    print("exact receipt verified: Gram positive; signed place faces and rational phase populations")


if __name__ == "__main__":
    main()
