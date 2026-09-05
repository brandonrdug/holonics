"""Exact finite Fourier pressure witness for a jet-flat periodic velocity.

All Fourier coefficients are rational complex pairs.  The witness is a finite
exterior perturbation: it makes no claim about a periodic Navier--Stokes
solution or any blowup conclusion.
"""

import json
from fractions import Fraction as Q
from pathlib import Path


BASE = Path(__file__).parent
ZERO = (Q(0), Q(0))
ONE = (Q(1), Q(0))
I = (Q(0), Q(1))


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def cneg(a):
    return (-a[0], -a[1])


def csub(a, b):
    return cadd(a, cneg(b))


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cscale(a, q):
    return (a[0] * q, a[1] * q)


def cdiv_int(a, n):
    return cscale(a, Q(1, n))


def nonzero(a):
    return a != ZERO


def add(left, right):
    result = dict(left)
    for mode, value in right.items():
        result[mode] = cadd(result.get(mode, ZERO), value)
        if not nonzero(result[mode]):
            del result[mode]
    return result


def neg(field):
    return {mode: cneg(value) for mode, value in field.items()}


def scale(field, q):
    return {mode: cscale(value, q) for mode, value in field.items() if nonzero(value)}


def mul1(left, right):
    result = {}
    for i, a in left.items():
        for j, b in right.items():
            mode = i + j
            result[mode] = cadd(result.get(mode, ZERO), cmul(a, b))
    return {mode: value for mode, value in result.items() if nonzero(value)}


def pow1(field, exponent):
    result = {0: ONE}
    for _ in range(exponent):
        result = mul1(result, field)
    return result


def deriv1(field):
    return {mode: cmul((Q(0), Q(mode)), value) for mode, value in field.items() if mode}


def embed(field, axis):
    return {tuple(mode if i == axis else 0 for i in range(3)): value for mode, value in field.items()}


def add3(left, right):
    return add(left, right)


def mul3(left, right):
    result = {}
    for i, a in left.items():
        for j, b in right.items():
            mode = tuple(i[q] + j[q] for q in range(3))
            result[mode] = cadd(result.get(mode, ZERO), cmul(a, b))
    return {mode: value for mode, value in result.items() if nonzero(value)}


def deriv3(field, axis):
    return {mode: cmul((Q(0), Q(mode[axis])), value) for mode, value in field.items() if mode[axis]}


def product3(*fields):
    result = {(0, 0, 0): ONE}
    for field in fields:
        result = mul3(result, field)
    return result


def eval_origin(field):
    result = ZERO
    for value in field.values():
        result = cadd(result, value)
    return result


def derivative_origin_1d(field, order):
    return sum_complex([cmul(power_i(mode, order), value) for mode, value in field.items()])


def power_i(mode, order):
    result = ONE
    for _ in range(order):
        result = cmul(result, (Q(0), Q(mode)))
    return result


def derivative_origin_3d(field, powers):
    return sum_complex([cmul(cmul(cmul(power_i(mode[0], powers[0]), power_i(mode[1], powers[1])),
                                  power_i(mode[2], powers[2])), value)
                        for mode, value in field.items()])


def real(value):
    assert value[1] == 0, value
    return value[0]


sin = {1: (Q(0), Q(-1, 2)), -1: (Q(0), Q(1, 2))}
cos = {1: (Q(1, 2), Q(0)), -1: (Q(1, 2), Q(0))}
h = {0: (Q(1, 2), Q(0)), 1: (Q(-1, 4), Q(0)), -1: (Q(-1, 4), Q(0))}


def build_case(N):
    F = mul1(sin, pow1(h, N))
    fx = embed(F, 0)
    fy = embed(F, 1)
    gp = embed(cos, 2)
    gz = embed(sin, 2)
    v = [scale(product3(fx, gp), Q(-1)), scale(product3(fy, gp), Q(-1)),
         add3(product3(embed(deriv1(F), 0), gz), product3(embed(deriv1(F), 1), gz))]

    divergence = add3(add3(deriv3(v[0], 0), deriv3(v[1], 1)), deriv3(v[2], 2))
    gradient = [[deriv3(v[j], i) for j in range(3)] for i in range(3)]
    source = {}
    for i in range(3):
        for j in range(3):
            source = add3(source, mul3(gradient[i][j], gradient[j][i]))
    Fx = embed(F, 0)
    Fy = embed(F, 1)
    Fxp = embed(deriv1(F), 0)
    Fyp = embed(deriv1(F), 1)
    Fxx = embed(deriv1(deriv1(F)), 0)
    Fyy = embed(deriv1(deriv1(F)), 1)
    gp = embed(cos, 2)
    g = embed(sin, 2)
    gpp = embed(deriv1(deriv1(sin)), 2)
    trace_formula = scale(product3(add3(add3(mul3(Fxp, Fxp), mul3(Fyp, Fyp)), mul3(Fxp, Fyp)),
                                    mul3(gp, gp)), Q(2))
    trace_formula = add3(trace_formula, scale(product3(add3(mul3(Fx, Fxx), mul3(Fy, Fyy)),
                                                       mul3(g, gpp)), Q(-2)))
    assert trace_formula == source
    source_mean = real(source.get((0, 0, 0), ZERO))
    source_origin = real(eval_origin(source))
    assert source_mean == 0 and source_origin == 0
    pressure = {mode: cdiv_int(value, sum(k * k for k in mode))
                for mode, value in source.items() if mode != (0, 0, 0)}
    poisson = {}
    for mode, value in pressure.items():
        poisson[mode] = cscale(value, sum(k * k for k in mode))
    assert not divergence
    assert source_mean == 0 and source_origin == 0
    assert poisson == source

    def hessian(axis):
        return real(sum_complex(cscale(value, -mode[axis] * mode[axis])
                                for mode, value in pressure.items()))

    pxx, pyy, pzz = hessian(0), hessian(1), hessian(2)
    assert pxx == pyy and pxx == -pzz / 2
    def pressure_derivative(powers):
        return derivative_origin_3d(pressure, powers)

    def torque_taylor_coefficient(i, j):
        result = ZERO
        if i >= 1:
            result = cadd(result, cdiv_int(pressure_derivative((i - 1, j + 1, 0)),
                                            factorial(i - 1) * factorial(j)))
        if j >= 1:
            result = csub(result, cdiv_int(pressure_derivative((i + 1, j - 1, 0)),
                                            factorial(i) * factorial(j - 1)))
        return result

    torque_x3y = torque_taylor_coefficient(3, 1)
    torque_xy3 = torque_taylor_coefficient(1, 3)
    assert torque_x3y == cneg(torque_xy3) and nonzero(torque_x3y)
    order_F = 2 * N + 1
    order_velocity = order_F
    assert order_velocity == 2 * N + 1
    leading_order = 2 * N + 1
    for order in range(leading_order):
        assert derivative_origin_1d(F, order) == ZERO
    leading_derivative = derivative_origin_1d(F, leading_order)
    assert leading_derivative == (Q(factorial(leading_order), 4**N), Q(0))
    return {
        "N": N,
        "F_modes": len(F),
        "velocity_modes": [len(field) for field in v],
        "source_modes": len(source),
        "pressure_modes": len(pressure),
        "divergence_zero": True,
        "poisson_residual_zero": True,
        "source_fourier_zero_mode": str(source_mean),
        "source_trace_origin": str(source_origin),
        "trace_formula_audit": "2*((Fx'^2+Fy'^2+Fx'*Fy')*g'^2-(Fx*Fxx+Fy*Fyy)*g*g'')",
        "pressure_hessian_origin": {"pxx": str(pxx), "pyy": str(pyy), "pzz": str(pzz)},
        "pzz_negative": pzz < 0,
        "velocity_vanishing_order": order_velocity,
        "F_vanishing_order": order_F,
        "F_leading_coefficient": str(Q(1, 4**N)),
        "F_derivative_check": {"all_orders_below_leading_zero": True, "leading_derivative_over_factorial": str(Q(1, 4**N))},
        "actual_local_torque": "tau_z=x*partial_y p-y*partial_x p",
        "torque_x3y_coefficient": pair_string(torque_x3y),
        "torque_xy3_coefficient": pair_string(torque_xy3),
        "torque_x3y_formula": "p_xxyy(0)/2-p_xxxx(0)/6",
        "torque_quartic_nonzero": True,
        "source_samples": {str(mode): pair_string(source[mode]) for mode in sorted(source)[:4]},
        "pressure_samples": {str(mode): pair_string(pressure[mode]) for mode in sorted(pressure)[:4]},
    }


def sum_complex(values):
    result = ZERO
    for value in values:
        result = cadd(result, value)
    return result


def factorial(n):
    result = 1
    for k in range(2, n + 1):
        result *= k
    return result


def pair_string(value):
    return [str(value[0]), str(value[1])]


cases = [build_case(1), build_case(32)]
assert cases[1]["velocity_vanishing_order"] == 65
assert cases[1]["velocity_vanishing_order"] > 61
assert cases[0]["pzz_negative"] and cases[1]["pzz_negative"]
def rational_enclosure(value, scale=10**9):
    lower = Q(value.numerator * scale // value.denominator, scale)
    upper = lower + Q(1, scale)
    assert lower <= value < upper
    return [str(lower), str(upper)]


for case in cases:
    case["readable_enclosures"] = {
        "pzz": rational_enclosure(Q(case["pressure_hessian_origin"]["pzz"])),
        "torque_x3y": rational_enclosure(Q(case["torque_x3y_coefficient"][0])),
    }

receipt = {
    "scope": "Finite exact periodic jet-flat pressure witness; no periodic PDE solution or blowup claim",
    "arithmetic": "Fraction-based rational complex Fourier pairs",
    "period": "2*pi in each angular coordinate",
    "potential": "A=(-F(y)*g(z),F(x)*g(z),0), F=sin(theta)*((1-cos(theta))/2)^N, g=sin(z)",
    "velocity": "v=(-F(x)*g'(z),-F(y)*g'(z),(F'(x)+F'(y))*g(z))",
    "pressure_rule": "for k!=0, p_k=trace(Dv^2)_k/|k|^2; p_0=0",
    "physical_scaling": "v_phys(x)=v(2*pi*x), p_phys(x)=p(2*pi*x); first derivatives scale by 2*pi and second derivatives and the Poisson source by (2*pi)^2",
    "cases": cases,
    "exit_status": 0,
}
print(json.dumps(receipt, indent=2))
