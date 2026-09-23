#!/usr/bin/env python3
"""Exact symbolic receipt for a two-translate Weil-square sign test.

Only integers and rational coefficients of sqrt(2) occur in the output.
The logarithm L=log(2) is retained as a formal positive factor.
"""

import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class QRoot2:
    rational: Fraction = Fraction(0)
    root2: Fraction = Fraction(0)

    def __add__(self, other):
        return QRoot2(self.rational + other.rational, self.root2 + other.root2)

    def __neg__(self):
        return QRoot2(-self.rational, -self.root2)

    def scale(self, scalar):
        scalar = Fraction(scalar)
        return QRoot2(scalar * self.rational, scalar * self.root2)

    def sign(self):
        a, b = self.rational, self.root2
        if a == 0:
            return (b > 0) - (b < 0)
        if b == 0 or (a > 0) == (b > 0):
            return (a > 0) - (a < 0)
        # Compare |a| and |b| sqrt(2) by squaring positive rationals.
        assert a * a != 2 * b * b
        dominant = a if a * a > 2 * b * b else b
        return (dominant > 0) - (dominant < 0)

    def packet(self):
        return {"rational": str(self.rational), "sqrt2": str(self.root2)}


def source_coefficient(c, address):
    return {0: 1, 1: c}.get(address, 0)


def autocorrelation(c, displacement):
    # Disjoint translates of a unit-L2 bump:
    # h(kL) = sum_j a_(j+k) a_j.
    return sum(
        source_coefficient(c, j + displacement) * source_coefficient(c, j)
        for j in (0, 1)
    )


def one_case(c):
    h = {str(k): autocorrelation(c, k) for k in (-2, -1, 0, 1, 2)}
    h0 = h["0"]
    h1 = h["1"]
    hm1 = h["-1"]
    # The n=2 term of truncatedPrimeReceiver is
    # (log 2)/sqrt(2) * (h(L)+h(-L)).
    prime_over_log2 = QRoot2(root2=Fraction(h1 + hm1, 2))
    # archimedeanIntegrand at L=log 2:
    # (h(0)/4 - h_even(L)/sqrt(2)) / (3/4).
    arch_at_log2 = (
        QRoot2(rational=Fraction(h0, 4))
        + QRoot2(root2=-Fraction(h1 + hm1, 4))
    ).scale(Fraction(4, 3))
    # For the even real bump, B=Phi(0)=Phi(1)>0. Both polar addresses
    # together equal B^2 * (4 + 3*c*sqrt(2)).
    polar_over_B_squared = QRoot2(rational=Fraction(4), root2=Fraction(3 * c))
    gram = [[h0, hm1], [h1, h0]]
    return {
        "relative_sign": c,
        "autocorrelation_at_k_log2": h,
        "address_gram": gram,
        "address_gram_determinant": h0 * h0 - h1 * hm1,
        "positive_square_decomposition": [
            {"linear_form": [1, c], "coefficient": 1},
            {"linear_form": [1, 0], "coefficient": 1},
            {"linear_form": [0, 1], "coefficient": 1},
        ],
        "prime_n2_coefficient_times_log2": prime_over_log2.packet(),
        "prime_n2_sign": prime_over_log2.sign(),
        "minus_prime_n2_sign": (-prime_over_log2).sign(),
        "archimedean_integrand_at_log2": arch_at_log2.packet(),
        "archimedean_integrand_sign": arch_at_log2.sign(),
        "polar_coefficient_times_B_squared": polar_over_B_squared.packet(),
        "polar_sign": polar_over_B_squared.sign(),
    }


def phase_population(denominator):
    rows = []
    counts = {}
    for k in range(-denominator, denominator + 1):
        c = Fraction(k, denominator)
        h0 = 1 + c * c
        gram_det = h0 * h0 - c * c
        prime = QRoot2(root2=c)
        arch = QRoot2(rational=h0 / 3, root2=-2 * c / 3)
        polar = QRoot2(rational=2 * h0, root2=3 * c)
        signs = {
            "prime": prime.sign(),
            "archimedean_at_log2": arch.sign(),
            "polar": polar.sign(),
        }
        label = "/".join(str(signs[key]) for key in
                         ("prime", "archimedean_at_log2", "polar"))
        counts[label] = counts.get(label, 0) + 1
        rows.append({
            "numerator": k,
            "relative_weight": str(c),
            "gram_determinant": str(gram_det),
            "signs": signs,
        })
    return {
        "common_denominator": denominator,
        "rows": rows,
        "sign_class_counts": counts,
    }


def main():
    packet = {
        "source": {
            "bump": "phi_eps=b_eps/sqrt(integral(b_eps^2)); b_eps(x)=exp(-1/(1-(x/eps)^2)) for |x|<eps and 0 otherwise",
            "eps": "1/16",
            "separation": "L=log(2)>1/2>2*eps",
            "prime_gap": "log(3/2)>1/3>2*eps, so h(log(n))=0 for every n>=3",
            "generator": "g_c(x)=phi_eps(x)+c*phi_eps(x-L), c real; negative c is a pi phase flip",
            "rational_population": "the same g_c for c=k/d, -d<=k<=d, d in {8,16}",
            "square": "h_c(t)=integral_R g_c(u+t)g_c(u)du",
            "spectral": "G_c(s)=Phi_eps(s)*(1+c*exp((s-1/2)*L)); H_c(s)=G_c(s)*conj(G_c(1-conj(s)))",
        },
        "scope": {
            "prime_cutoff": "every N>=2; only n=2 contributes",
            "archimedean": "pointwise integrand at x=L only; complete integral is not evaluated",
            "positive_receiver": "two-address autocorrelation Gram, not the xi zero divisor",
            "global_weil_positivity": "unresolved",
        },
        "cases": [one_case(-1), one_case(1)],
        "phase_populations": [phase_population(8), phase_population(16)],
    }
    target = Path(__file__).with_name("receipt.json")
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")
    print(target)


if __name__ == "__main__":
    main()
