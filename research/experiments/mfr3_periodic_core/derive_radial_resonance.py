"""Exact rational Taylor recurrence for the first radial resonance test.

This is a finite symbolic witness.  It does not assert a PDE solution or stability estimate.
All rows use the Cartesian axisymmetric coefficients from NavierStokesAxisymmetricChart.
"""

import json

import sympy as sp


z, r = sp.symbols("z r", real=True)
alpha = sp.Rational(3, 2)
beta = sp.Integer(1)
p = sp.Rational(5, 2)
kappa = sp.Rational(7, 2)
MAX_M = 14


def trunc(expr, degree):
    return sp.series(expr, z, 0, degree + 1).removeO().expand()


def coeff(poly, power):
    return sp.expand(poly).coeff(z, power)


def solve_rows(equation, unknowns, degree, label, rows):
    """Solve a linear coefficient row, preserving zero-coefficient compatibility rows."""
    scalar_rows = []
    scalar_equations = []
    for j in range(degree + 1):
        e = sp.expand(equation).coeff(z, j)
        if e != 0:
            scalar_equations.append(e)
            scalar_rows.append({
                "power": j,
                "equation": sp.sstr(e),
                "linear_coefficients": {
                    str(u): sp.sstr(sp.expand(e).coeff(u)) for u in unknowns
                },
            })
    # Keep the original expressions for solving: reparsing receipt strings can
    # recreate a symbolic parameter with different assumptions (e.g. X>0).
    equations = scalar_equations
    if not equations:
        rows.append({
            "label": label,
            "status": "empty",
            "unknowns": [str(x) for x in unknowns],
            "scalar_rows": scalar_rows,
        })
        return {}
    matrix, rhs = sp.linear_eq_to_matrix(equations, unknowns)
    free_unknowns = [
        str(u) for j, u in enumerate(unknowns)
        if all(matrix[i, j] == 0 for i in range(matrix.rows))
    ]
    zero_rows = []
    for i in range(matrix.rows):
        if all(matrix[i, j] == 0 for j in range(matrix.cols)):
            zero_rows.append({"forcing": sp.sstr(rhs[i]), "vanishes": rhs[i] == 0})
    rows.append({
        "label": label,
        "status": "solved" if not zero_rows else "compatibility_rows",
        "unknowns": [str(x) for x in unknowns],
        "zero_rows": zero_rows,
        "rank": int(matrix.rank()),
        "unknown_count": len(unknowns),
        "scalar_rows": scalar_rows,
        "free_unknowns": free_unknowns,
    })
    result = sp.linsolve(equations, unknowns)
    if result == sp.EmptySet:
        # Preserve the first solvable coefficients, then retain the exact incompatible forcing
        # when a resonant row has zero linear coefficient.
        partial = {}
        residual_rows = []
        for equation in equations:
            equation = sp.expand(equation.subs(partial))
            free = [u for u in unknowns if u not in partial and equation.coeff(u) != 0]
            if free:
                variable = free[0]
                value = sp.solve(equation, variable, dict=False)[0]
                partial[variable] = sp.simplify(value)
            elif equation != 0:
                residual_rows.append(sp.simplify(equation))
        rows[-1]["status"] = "incompatible"
        rows[-1]["forcing_rows"] = [sp.sstr(e) for e in residual_rows]
        rows[-1]["forcing_vanishes"] = [e == 0 for e in residual_rows]
        rows[-1]["partial_solution"] = {str(u): sp.sstr(v) for u, v in partial.items()}
        return partial
    tuple_solution = next(iter(result))
    return {u: v for u, v in zip(unknowns, tuple_solution) if v != u}


# Baseline exact Taylor polynomials, with F0 even and W0 odd.
NF = lambda m: 30 - 2 * m
NW = lambda m: 31 - 2 * m
F0 = trunc((1 + z**2) ** (-p / 2), NF(0))
I0 = sp.integrate(trunc((1 + z**2) ** sp.Rational(5, 4), NW(0) + 2), (z, 0, z))
W0 = trunc(kappa * F0 * I0 - z, NW(0))

if __name__ == "__main__":
    F = [F0]
    W = [W0]
    V = [-sp.diff(W0, z) / 2]
    rows = []


    def radial_A(rmode):
        out = (alpha + beta) * V[rmode]
        out += sum(W[i] * sp.diff(V[rmode - i], z) for i in range(rmode + 1))
        if rmode >= 0:
            out += beta * z * sp.diff(V[rmode], z)
        if rmode >= 1:
            out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                           (rmode - i) * V[rmode - i]
                           for i in range(rmode))
        out += sum(V[i] * V[rmode - i] for i in range(rmode + 1))
        out -= sum(F[i] * F[rmode - i] for i in range(rmode + 1))
        return sp.expand(out)


    def axial_B(rmode):
        out = alpha * W[rmode]
        out += sum(W[i] * sp.diff(W[rmode - i], z) for i in range(rmode + 1))
        out += beta * z * sp.diff(W[rmode], z)
        if rmode >= 1:
            out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                           (rmode - i) * W[rmode - i]
                           for i in range(rmode))
        return sp.expand(out)


    def swirl_C(rmode):
        out = (alpha + beta) * F[rmode]
        out += 2 * sum(V[i] * F[rmode - i] for i in range(rmode + 1))
        out += sum(W[i] * sp.diff(F[rmode - i], z) for i in range(rmode + 1))
        out += beta * z * sp.diff(F[rmode], z)
        if rmode >= 1:
            out += 2 * sum((V[i] + (beta if i == 0 else 0)) *
                           (rmode - i) * F[rmode - i]
                           for i in range(rmode))
        return sp.expand(out)


    for m in range(1, MAX_M + 1):
        wvars = [sp.Symbol(f"W{m}_{j}") for j in range(1, NW(m) + 1, 2)]
        fvars = [sp.Symbol(f"F{m}_{j}") for j in range(0, NF(m) + 1, 2)]
        W.append(sum(v * z**j for v, j in zip(wvars, range(1, NW(m) + 1, 2))))
        V.append(-sp.diff(W[m], z) / (2 * (m + 1)))
        F.append(sum(v * z**j for v, j in zip(fvars, range(0, NF(m) + 1, 2))))

        pressure_eq = trunc(sp.diff(radial_A(m - 1), z) - 2 * m * axial_B(m), NW(m) + 1)
        wsol = solve_rows(pressure_eq, wvars, NW(m), f"W{m} pressure", rows)
        W[m] = sp.expand(W[m].subs(wsol))
        V[m] = sp.expand(V[m].subs(wsol))

        swirl_eq = trunc(swirl_C(m), NF(m))
        fsol = solve_rows(swirl_eq, fvars, NF(m), f"F{m} swirl", rows)
        F[m] = sp.expand(F[m].subs(fsol))

    # Recompute every committed residual row after all prior substitutions.
    pressure_residuals = []
    swirl_residuals = []
    for m in range(1, MAX_M + 1):
        pressure_residuals.append(sp.simplify(trunc(sp.diff(radial_A(m - 1), z) - 2 * m * axial_B(m), NW(m) + 1)))
        swirl_residuals.append(sp.simplify(trunc(swirl_C(m), NF(m))))

    for m, residual in enumerate(pressure_residuals, 1):
        assert residual == 0, ("pressure residual", m, residual)
    for m, residual in enumerate(swirl_residuals, 1):
        # F14 is the expected first parity-allowed resonant row; retain its exact forcing.
        if m != 14:
            assert residual == 0, ("swirl residual", m, residual)

    f14_z2 = sp.expand(swirl_residuals[13]).coeff(z, 2)
    assert f14_z2 != 0

    receipt = {
        "scope": "Finite exact Taylor recurrence through radial mode 14; reflection-symmetric F even and W odd; no PDE existence or stability claim",
        "sympy_version": sp.__version__,
        "parameters": {"alpha": sp.sstr(alpha), "beta": sp.sstr(beta), "p": sp.sstr(p), "kappa": sp.sstr(kappa)},
        "budgets": {"N_F(m)": "30-2*m", "N_W(m)": "31-2*m", "max_radial_mode": 14},
        "baseline": {"F0": "(1+z^2)^(-5/4)", "W0": "(7/2)*F0*integral(1/F0)-z"},
        "committed_formulas": {
            "divergence": "2*V+2*s*V_s+W_z",
            "pressure_equation": "A_(m-1)'=2*m*B_m",
            "swirl_equation": "C_m=0",
            "V_m": "-W_m'/(2*(m+1))",
        },
        "row_receipts": rows,
        "residual_recompute": {"pressure_all_zero": True, "swirl_m1_to_m13_zero": True, "swirl_m14_z2": sp.sstr(f14_z2)},
        "resonance": {"row": 14, "coefficient": "F14_z2", "forcing": sp.sstr(f14_z2), "forcing_vanishes": False},
        "exit_status": 0,
    }
    print(json.dumps(receipt, indent=2))
