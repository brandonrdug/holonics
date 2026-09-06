"""Shared exact order-three periodic initial spectrum and potential."""

import sympy as sp


I = sp.I
rho = sp.symbols("rho", real=True)
x, y, z = sp.symbols("x y z", real=True)
a = sp.Rational(10, 3)
nu = sp.Integer(1)
q = sp.Rational(1, 3)


def add(left, right):
    out = dict(left)
    for mode, value in right.items():
        out[mode] = sp.expand(out.get(mode, 0) + value)
        if out[mode] == 0:
            del out[mode]
    return out


def mul(left, right):
    out = {}
    for i, left_value in left.items():
        for j, right_value in right.items():
            mode = tuple(i[k] + j[k] for k in range(3))
            out[mode] = out.get(mode, 0) + left_value * right_value
    return {mode: sp.expand(value) for mode, value in out.items() if sp.expand(value) != 0}


def mul1(left, right):
    out = {}
    for i, left_value in left.items():
        for j, right_value in right.items():
            out[i + j] = out.get(i + j, 0) + left_value * right_value
    return {mode: sp.expand(value) for mode, value in out.items() if sp.expand(value) != 0}


def embed(field, axis):
    return {tuple(mode if k == axis else 0 for k in range(3)): value for mode, value in field.items()}


def deriv(field, axis):
    return {mode: I * mode[axis] * value for mode, value in field.items() if mode[axis]}


def deriv1(field):
    return {mode: I * mode * value for mode, value in field.items() if mode}


def eval0(field):
    return sp.expand(sum(field.values()))


def jet_at_origin(field, powers):
    return sp.expand(sum((I * mode[0]) ** powers[0] * (I * mode[1]) ** powers[1]
                         * (I * mode[2]) ** powers[2] * value for mode, value in field.items()))


sin = {1: -I / 2, -1: I / 2}
sin2 = {2: -I / 2, -2: I / 2}
sin3 = {3: -I / 2, -3: I / 2}
cos = {1: sp.Rational(1, 2), -1: sp.Rational(1, 2)}
cos2 = {2: sp.Rational(1, 2), -2: sp.Rational(1, 2)}
cos3 = {3: sp.Rational(1, 2), -3: sp.Rational(1, 2)}
F = add(add({n: sp.Rational(3, 2) * v for n, v in sin.items()},
            {n: sp.Rational(-3, 10) * v for n, v in sin2.items()}),
        {n: sp.Rational(1, 30) * v for n, v in sin3.items()})
C = deriv1(F)
one = {0: sp.Integer(1)}
one_minus_cos = add(one, {n: -v for n, v in cos.items()})
cutoff = add(one, {n: rho * v for n, v in mul1(mul1(one_minus_cos, one_minus_cos), one_minus_cos).items()})

# psi_y and -psi_x for the five solved rational coefficients.
A, BB, CC, DD, EE = sp.Rational(169, 216), sp.Rational(-4, 135), sp.Rational(11, 3240), sp.Rational(7, 27), sp.Rational(1, 108)
Vx = add(add(add({n: -A * v for n, v in embed(sin, 1).items()},
                {n: -2 * BB * v for n, v in embed(sin2, 1).items()}),
            {n: -3 * CC * v for n, v in embed(sin3, 1).items()}),
        add({n: -DD * v for n, v in mul(embed(cos, 0), embed(sin, 1)).items()},
            {n: -EE * v for n, v in mul(embed(cos2, 0), embed(sin, 1)).items()}))
Vx = add(Vx, {n: -2 * EE * v for n, v in mul(embed(cos, 0), embed(sin2, 1)).items()})
Vy = add(add({n: A * v for n, v in embed(sin, 0).items()},
             {n: 2 * BB * v for n, v in embed(sin2, 0).items()}),
         {n: 3 * CC * v for n, v in embed(sin3, 0).items()})
Vy = add(Vy, {n: DD * v for n, v in mul(embed(sin, 0), embed(cos, 1)).items()})
Vy = add(add(Vy, {n: 2 * EE * v for n, v in mul(embed(sin2, 0), embed(cos, 1)).items()}),
         {n: EE * v for n, v in mul(embed(sin, 0), embed(cos2, 1)).items()})
psi = add(add({n: A * v for n, v in add(embed(cos, 0), embed(cos, 1)).items()},
              {n: BB * v for n, v in add(embed(cos2, 0), embed(cos2, 1)).items()}),
          {n: CC * v for n, v in add(embed(cos3, 0), embed(cos3, 1)).items()})
psi = add(add(psi, {n: DD * v for n, v in mul(embed(cos, 0), embed(cos, 1)).items()}),
          {n: EE * v for n, v in add(mul(embed(cos2, 0), embed(cos, 1)),
                                     mul(embed(cos, 0), embed(cos2, 1))).items()})
psi_expression = (A * (sp.cos(x) + sp.cos(y)) + BB * (sp.cos(2 * x) + sp.cos(2 * y))
                  + CC * (sp.cos(3 * x) + sp.cos(3 * y)) + DD * sp.cos(x) * sp.cos(y)
                  + EE * (sp.cos(2 * x) * sp.cos(y) + sp.cos(x) * sp.cos(2 * y)))
eps = sp.symbols("eps")
psi_target = psi_expression.subs({x: 0, y: 0}) - (x**2 + y**2) / 2 + (x**2 + y**2)**2 / 24 - (x**2 + y**2)**3 / 324
assert sp.expand(sp.series(psi_expression.subs({x: eps * x, y: eps * y}), eps, 0, 8).removeO()
                 - psi_target.subs({x: eps * x, y: eps * y})).is_zero
S = [{n: -a * sp.Rational(1, 2) * v for n, v in mul(mul(embed(F, 0), embed(C, 1)), embed(C, 2)).items()},
     {n: -a * sp.Rational(1, 2) * v for n, v in mul(mul(embed(C, 0), embed(F, 1)), embed(C, 2)).items()},
     {n: a * v for n, v in mul(mul(embed(C, 0), embed(C, 1)), embed(F, 2)).items()}]
u = [add(S[0], mul(embed(cutoff, 2), Vx)), add(S[1], mul(embed(cutoff, 2), Vy)), S[2]]
A_phase = [
    {n: -a * sp.Rational(1, 2) * v for n, v in mul(mul(embed(C, 0), embed(F, 1)), embed(F, 2)).items()},
    {n: a * sp.Rational(1, 2) * v for n, v in mul(mul(embed(F, 0), embed(C, 1)), embed(F, 2)).items()},
    mul(embed(cutoff, 2), psi),
]
curl_A = [add(deriv(A_phase[2], 1), {n: -v for n, v in deriv(A_phase[1], 2).items()}),
          add(deriv(A_phase[0], 2), {n: -v for n, v in deriv(A_phase[2], 0).items()}),
          add(deriv(A_phase[1], 0), {n: -v for n, v in deriv(A_phase[0], 1).items()})]
assert all(sp.expand(curl_A[i].get(mode, 0) - u[i].get(mode, 0)) == 0
           for i in range(3) for mode in set(curl_A[i]) | set(u[i]))
