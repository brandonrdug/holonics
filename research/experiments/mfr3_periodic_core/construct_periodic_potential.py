"""Return the actual finite polynomial potential behind the retained MFR3 core.

This is a construction of fields, not a radial-convergence or stability receipt.
Every coefficient is exact; X is kept symbolic with its already-certified root
condition. No numeric root or discarded nonlinear product defines this field.
The full field retains all terms of the finite potential, including terms whose
PDE residual was outside the earlier Taylor apertures.
"""

import contextlib
import io
import json
import runpy
from pathlib import Path

from flint import fmpq as Q

BASE = Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    response = runpy.run_path(str(BASE / "derive_first_viscous_response.py"))
full = response["full"]


def poly(p):
    return {str(i): str(c) for i, c in enumerate(p.coeffs()) if c}


def carrier(value, scale, kind):
    names = {"c": "constant", "d": "Y"} if kind == "euler" else {
        "c": "constant", "e": "E", "y": "Y", "t": "T", "k": "eliminated_K"}
    result = {name: poly(getattr(value, slot) * scale) for slot, name in names.items()
              if getattr(value, slot)}
    assert "eliminated_K" not in result
    return result


def terms(series, viscous_order, radial_offset, sign, kind):
    result = []
    for m, row in enumerate(series):
        for n, value in sorted(row.items()):
            coefficient = carrier(value, Q(sign, 2 * (m + 1)), kind)
            if coefficient:
                result.append({"s": m + radial_offset, "z": n, "mu": viscous_order,
                               "coefficient": coefficient})
    return result


h = terms(full["W"], 0, 0, 1, "euler") + terms(response["W"], 1, 0, 1, "viscous")
ag = terms(full["J"], 0, 1, -1, "euler") + terms(response["K"], 1, 1, -1, "viscous")
# The mode-28 homogeneous angular coefficient was represented by zero in the
# previous finite recurrence. Return its complete surviving fibre in the field.
ag.append({"s": 29, "z": 4, "mu": 0, "coefficient": {"L": {"0": "-1/58"}}})


def recover(terms, angular):
    """Differentiate -2(ag)_s or 2h+2s*h_s coefficient by coefficient."""
    result = []
    for term in terms:
        exponent = term["s"]
        factor = -2 * exponent if angular else 2 * (exponent + 1)
        result.append({"s": exponent - 1 if angular else exponent,
                       "z": term["z"], "mu": term["mu"],
                       "coefficient": {
                           name: {i: str(Q(c) * factor) for i, c in coefficients.items()}
                           for name, coefficients in term["coefficient"].items()}})
    return result


def original(series, order, kind):
    return [{"s": m, "z": n, "mu": order, "coefficient": carrier(value, Q(1), kind)}
            for m, row in enumerate(series) for n, value in sorted(row.items()) if value]


assert recover(h, False) == original(full["W"], 0, "euler") + original(response["W"], 1, "viscous")
assert recover(ag, True)[:-1] == original(full["J"], 0, "euler") + original(response["K"], 1, "viscous")
assert recover(ag, True)[-1] == {
    "s": 28, "z": 4, "mu": 0, "coefficient": {"L": {"0": "1"}}}

receipt = {
    "grade": "established-bounded", "evidence": ["computational-witness"],
    "scope": "Actual finite polynomial vector potential; no full PDE residual closure or stability claim",
    "coefficient_convention": "sum coefficient(X,Y,E,T,L)*mu^j*s^m*z^n; coefficient slots are affine in named parameters and polynomial in X",
    "selectors": {
        "X": "unique positive root in (5625/2236,1366/543) of the first compatibility polynomial",
        "first_compatibility_polynomial": poly(full["P"]),
        "a": "positive sqrt(X)",
        "Y": {"numerator": poly(-full["Q28"]), "denominator": poly(full["R"])},
        "E": {"numerator": poly(response["E_numerator"]), "denominator": poly(response["E_denominator"])},
        "free": ["T=W1_14[z]", "L=J0_28[z^4]"],
        "mu": "nu*q/ell; 0<=mu<=1/10000000 is the earlier axis-shape interval, not a global residual bound"},
    "h": h, "a_times_g": ag,
    "local_potential": "A=(-y*h(s,z),x*h(s,z),g(s,z)); s=x^2+y^2; g=(a_times_g)/a",
    "local_velocity": "curl A=(x*V-y*Omega,y*V+x*Omega,W), V=-h_z, Omega=-2*g_s, W=2*h+2*s*h_s",
    "physical_potential": "B(x)=(ell/q)*A(x/ell), ell>0,q>0; curl B=(1/q)*U(x/ell)",
    "periodic_completion": "curl periodize(b*B), where b is the actual ContDiffBump(0) with rIn=ell/8,rOut=ell/4, 0<ell<2; periodize sums integer lattice translates",
    "core_agreement": "physical velocity equals q^(-1)*U(x/ell) on |x|<ell/8, including every actual derivative there",
    "pressure": "mean-zero periodic inverse of -Laplacian applied to trace(Du^2), for the COMPLETE constructed velocity; local radial pressure is only a comparison",
    "checks": {"axial_velocity_recovered_exactly": True, "angular_velocity_recovered_exactly": True,
               "surviving_angular_fibre_retained": True, "h_terms": len(h), "a_times_g_terms": len(ag)},
    "open": ["complete nonlocal pressure/residual for this full core", "quantitative linear and nonlinear control", "physical endpoint for a controlled exact continuation"]}
print(json.dumps(receipt, indent=2))
