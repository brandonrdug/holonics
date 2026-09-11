"""Exterior rational π/e receivers; no native inference or floating arithmetic.

Machin and BBP use their classical identities. All finite states, tail bounds,
floor decisions, and cross-generator comparisons below use integers/Fraction.
Offsets count digits AFTER the radix point, starting at zero. BBP keeps a
modular representative of 16**offset * π rather than constructing its prefix.
Run with --output PATH to retain the complete rational receipts as JSON.
"""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


def floor(x):
    return x.numerator // x.denominator


def bits(x):
    return max(abs(x.numerator).bit_length(), x.denominator.bit_length())


def encode(n, base, width):
    alphabet = "0123456789ABCDEF"
    digits = []
    for _ in range(width):
        n, d = divmod(n, base)
        digits.append(alphabet[d])
    assert n == 0
    return "".join(reversed(digits))


def read_window(lower, upper, base, offset, width):
    """Equal UNREDUCED endpoint floors certify the entire interval."""
    assert lower <= upper and base in (10, 16) and offset >= 0 and width > 0
    scale = base ** (offset + width)
    left, right = floor(scale * lower), floor(scale * upper)
    if left != right:
        return None
    return {"digits": encode(left % base**width, base, width),
            "scaled_floor": left, "lower": str(lower), "upper": str(upper),
            "width_of_interval": str(upper - lower)}


def machin(base, offset, width):
    # a[n+1]/a[n] = -(2n+1)/(b²(2n+3)), b in {5,239}.
    terms = [Q(1, 5), Q(1, 239)]
    sums = [Q(0), Q(0)]
    n, peak = 0, 0
    snapshots = []
    while True:
        for j, b in enumerate((5, 239)):
            sums[j] += terms[j]
            terms[j] *= Q(-(2 * n + 1), b * b * (2 * n + 3))
        n += 1
        lows = [s + min(Q(0), a) for s, a in zip(sums, terms)]
        highs = [s + max(Q(0), a) for s, a in zip(sums, terms)]
        lower, upper = 16 * lows[0] - 4 * highs[1], 16 * highs[0] - 4 * lows[1]
        peak = max(peak, *(bits(x) for x in [*sums, *terms, lower, upper]))
        face = read_window(lower, upper, base, offset, width)
        if n & (n - 1) == 0 or face:
            snapshots.append({"n": n, "partial_sums": list(map(str, sums)),
                              "next_terms": list(map(str, terms)),
                              "lower": str(lower), "upper": str(upper),
                              "receiver_determined": face is not None})
        if face:
            return {"generator": "Machin", "base": base, "offset": offset,
                    "width": width, "terms_per_arctan": n,
                    "terms_total": 2 * n, "max_recorded_rational_bits": peak,
                    "snapshots": snapshots, **face}


def factorial_e(offset, width):
    n, partial, term, peak = 0, Q(0), Q(1), 0
    snapshots = []
    while True:
        partial += term
        n += 1
        term /= n
        # Next term 1/n!, all later ratios <= 1/(n+1).
        lower, upper = partial, partial + term * Q(n + 1, n)
        peak = max(peak, *(bits(x) for x in (partial, term, upper)))
        face = read_window(lower, upper, 10, offset, width)
        if n & (n - 1) == 0 or face:
            snapshots.append({"n": n, "partial_sum": str(partial),
                              "next_term": str(term), "lower": str(lower),
                              "upper": str(upper), "receiver_determined": face is not None})
        if face:
            return {"generator": "factorial e", "base": 10, "offset": offset,
                    "width": width, "terms_total": n,
                    "max_recorded_rational_bits": peak, "snapshots": snapshots, **face}


def bbp(offset, width):
    coefficients = {1: 4, 4: -2, 5: -1, 6: -1}
    parts = {}
    peak = 0
    for m in coefficients:
        value = Q(0)
        for k in range(offset + 1):
            denominator = 8 * k + m
            # pow uses modular exponentiation; no prefix digit computation.
            value += Q(pow(16, offset - k, denominator), denominator)
            peak = max(peak, bits(value))
        parts[m] = value
    modular_prefix = {str(m): str(v) for m, v in parts.items()}
    t = 0
    snapshots = []
    while True:
        total = sum((c * parts[m] for m, c in coefficients.items()), Q(0))
        bounds = {m: Q(1, 16**t * 15 * (8 * (offset + t + 1) + m))
                  for m in coefficients}
        lower = total - 2 * bounds[4] - bounds[5] - bounds[6]
        upper = total + 4 * bounds[1]
        peak = max(peak, *(bits(x) for x in [*parts.values(), total, lower, upper]))
        # offset already applied by the modular decomposition.
        face = read_window(lower, upper, 16, 0, width)
        snapshots.append({"tail_terms_per_component": t,
                          "scaled_modular_sum": str(total),
                          "lower": str(lower), "upper": str(upper),
                          "receiver_determined": face is not None})
        if face:
            return {"generator": "BBP modular window", "base": 16,
                    "offset": offset, "width": width,
                    "prefix_modular_terms": 4 * (offset + 1),
                    "tail_terms_total": 4 * t,
                    "max_recorded_rational_bits": peak,
                    "modular_prefix_components": modular_prefix,
                    "interval_chart": "16^offset*pi modulo an integer",
                    "snapshots": snapshots, **face}
        t += 1
        for m in coefficients:
            parts[m] += Q(1, 16**t * (8 * (offset + t) + m))


def receiver_controls():
    # Equal residues at endpoints can conceal a complete turn across digit cells.
    assert floor(Q(0)) % 16 == floor(Q(16)) % 16
    assert read_window(Q(0), Q(1), 16, 0, 1) is None
    cycle, moved_cycle = (2, 3), (5, 3)  # T = [[1,1],[0,1]]
    probes = ((1, 0), (0, 1), (3, -2))
    rows = []
    for a, b in probes:
        moved_probe = (a, b - a)  # inverse transpose of T
        original = a * cycle[0] + b * cycle[1]
        moved = moved_probe[0] * moved_cycle[0] + moved_probe[1] * moved_cycle[1]
        assert original == moved
        rows.append({"cycle": cycle, "probe": (a, b), "reading": original,
                     "moved_cycle": moved_cycle, "moved_probe": moved_probe,
                     "moved_reading": moved})
    return {"wraparound_rejected": True, "torus_covariance": rows}


def arithmetic_controls():
    def factor(n):
        result, p = {}, 2
        while p * p <= n:
            while n % p == 0:
                result[p] = result.get(p, 0) + 1
                n //= p
            p += 1
        if n > 1:
            result[n] = result.get(n, 0) + 1
        return result

    def gaussian_mul(z, w):
        a, b = z
        c, d = w
        return a * c - b * d, a * d + b * c

    square = gaussian_mul((5, 1), (5, 1))
    fourth = gaussian_mul(square, square)
    closure = gaussian_mul((239, 1), (2, 2))
    assert fourth == closure == (476, 480)
    # Euler's positive product: omitted integers all exceed the aperture N,
    # hence zeta(2)-P_N <= sum_{n>N} 1/n² <= 1/N.
    aperture = 31  # Declared finite comparison aperture, not intrinsic capacity.
    primes = [n for n in range(2, aperture + 1) if factor(n) == {n: 1}]
    product = Q(1)
    for p in primes:
        product *= Q(p * p, p * p - 1)
    lower, upper = 6 * product, 6 * (product + Q(1, aperture))
    pi_receipt = machin(10, 0, 12)
    pi_lower, pi_upper = Q(pi_receipt["lower"]), Q(pi_receipt["upper"])
    assert lower < pi_lower * pi_lower <= pi_upper * pi_upper < upper
    ratios = []
    for n in range(8):
        r = Q(-(2 * n + 1), 25 * (2 * n + 3))
        ratios.append({"n": n, "ratio": str(r),
                       "numerator_prime_factors": factor(abs(r.numerator)),
                       "denominator_prime_factors": factor(r.denominator)})
    return {"gaussian_fourth_power_and_closure": fourth,
            "norm_5_plus_i": factor(26), "norm_239_plus_i": factor(57122),
            "arctan_1_over_5_ratio_currents": ratios,
            "zeta2_prime_product_aperture": aperture, "primes": primes,
            "partial_prime_product": str(product), "pi_squared_lower": str(lower),
            "pi_squared_upper": str(upper), "machin_interval_square_contained": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipts, comparisons = [], []
    for offset in (0, 12):
        receipts.extend((machin(10, offset, 12), factorial_e(offset, 12)))
    for offset in (0, 32, 128):
        direct, prefix = bbp(offset, 8), machin(16, offset, 8)
        # Validation only: neither generator's refinement reads the other's result.
        assert direct["digits"] == prefix["digits"]
        receipts.extend((direct, prefix))
        comparisons.append({"offset": offset, "width": 8,
                            "BBP_equals_Machin": True, "digits": direct["digits"]})
    result = {"scope": "exterior exact-rational algorithm and receiver witnesses",
              "identity_dependencies": ["Machin identity", "BBP identity", "exp factorial series"],
              "certification": "analytic tail enclosure plus equal unreduced endpoint floors",
              "controls": receiver_controls(), "arithmetic_controls": arithmetic_controls(),
              "comparisons": comparisons, "receipts": receipts}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    for row in receipts:
        print(json.dumps({k: v for k, v in row.items()
                          if k in {"generator", "base", "offset", "width", "digits",
                                   "terms_total", "prefix_modular_terms", "tail_terms_total",
                                   "max_recorded_rational_bits"}}))


if __name__ == "__main__":
    main()
