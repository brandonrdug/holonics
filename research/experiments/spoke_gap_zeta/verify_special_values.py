#!/usr/bin/env python3
"""Check the pentagonal special values used beside the spoke-gap receipt.

This is an exterior high-precision numerical witness.  It is not an interval
certificate and does not enter native inference or engine code.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80
ROOT = Path(__file__).resolve().parent


def fmt(value: mp.mpf) -> str:
    return mp.nstr(value, 45)


def residual(left: mp.mpf, right: mp.mpf) -> dict[str, str]:
    return {"left": fmt(left), "right": fmt(right), "absolute": fmt(abs(left - right))}


def zeta_derivative_at_zero(a: mp.mpf) -> mp.mpf:
    return mp.diff(lambda s: mp.zeta(s, a), 0)


def finite_dynamical_zeta() -> dict[str, str | int]:
    z = mp.mpf("0.1")
    phi = (1 + mp.sqrt(5)) / 2
    n_max = 80
    finite_log = mp.fsum(
        [
            ((phi * z) ** n + (-phi ** -1 * z) ** n) / n
            for n in range(1, n_max + 1)
        ]
    )
    finite_value = mp.exp(finite_log)
    exact_value = 1 / (1 - z - z**2)
    rho = phi * z
    sigma = phi**-1 * z
    tail_log_bound = rho ** (n_max + 1) / ((n_max + 1) * (1 - rho)) + sigma ** (n_max + 1) / ((n_max + 1) * (1 - sigma))
    value_error_bound = mp.exp(tail_log_bound) - 1
    return {
        "matrix": "[[0,1],[1,1]]",
        "z": fmt(z),
        "n_max": n_max,
        "finite_exp_sum": fmt(finite_value),
        "closed_form": fmt(exact_value),
        "absolute_residual": fmt(abs(finite_value - exact_value)),
        "declared_log_tail_bound": fmt(tail_log_bound),
        "derived_relative_value_tail_bound": fmt(value_error_bound),
    }


def main() -> None:
    one_fifth = mp.mpf(1) / 5
    two_fifths = mp.mpf(2) / 5
    three_fifths = mp.mpf(3) / 5
    four_fifths = mp.mpf(4) / 5
    phi = (1 + mp.sqrt(5)) / 2
    log_phi = mp.log(phi)
    gamma_ratio = mp.gamma(one_fifth) * mp.gamma(four_fifths) / (mp.gamma(two_fifths) * mp.gamma(three_fifths))
    zeta_log_ratio = (
        zeta_derivative_at_zero(one_fifth)
        + zeta_derivative_at_zero(four_fifths)
        - zeta_derivative_at_zero(two_fifths)
        - zeta_derivative_at_zero(three_fifths)
    )
    digamma_l = -(mp.digamma(one_fifth) - mp.digamma(two_fifths) - mp.digamma(three_fifths) + mp.digamma(four_fifths)) / 5
    digamma_target = 2 * log_phi / mp.sqrt(5)
    li2_inverse = mp.polylog(2, phi**-1)
    li2_inverse_target = 3 * mp.zeta(2) / 5 - log_phi**2
    li2_inverse_square = mp.polylog(2, phi**-2)
    li2_inverse_square_target = 2 * mp.zeta(2) / 5 - log_phi**2
    data = {
        "schema": "holonics.spoke-gap-zeta.special-values.v1",
        "precision_decimal_digits": 80,
        "scope": "Exterior mpmath numerical witness; decimal residuals are not outward interval certificates.",
        "source_anchor": "formal/elementary-holonics/ElementaryHolonics/Millennium/FiveTheta.lean",
        "values": {
            "phi": fmt(phi),
            "gamma_ratio_equals_phi": residual(gamma_ratio, phi),
            "zeta_derivative_log_ratio_equals_log_phi": residual(zeta_log_ratio, log_phi),
            "L1_chi5_equals_2_log_phi_over_sqrt5": residual(digamma_l, digamma_target),
            "Li2_phi_inverse": residual(li2_inverse, li2_inverse_target),
            "Li2_phi_inverse_square": residual(li2_inverse_square, li2_inverse_square_target),
        },
        "finite_dynamical_zeta": finite_dynamical_zeta(),
    }
    output = ROOT / "special_values.json"
    output.write_text(json.dumps(data, indent=2) + "\n")
    for name, check in data["values"].items():
        if isinstance(check, dict) and "absolute" in check:
            print(f"{name}: residual {check['absolute']}")
    print(f"finite_dynamical_zeta: residual {data['finite_dynamical_zeta']['absolute_residual']}")


if __name__ == "__main__":
    main()
