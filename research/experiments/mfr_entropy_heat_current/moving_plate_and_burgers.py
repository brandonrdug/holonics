"""Exact moving-plate and heat/log-current joins, extending the existing MFR source audit.

This is symbolic exterior verification of the displayed differential identities. The polynomial
quartet is a supplied source control, not the xi function or an RH result. No raster is generated.
"""
import argparse
import json
from pathlib import Path
from time import perf_counter_ns
import sympy as sp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    started = perf_counter_ns()
    checks = {}

    def zero(name, expression):
        residual = sp.cancel(sp.expand(expression))
        assert residual == 0, (name, residual)
        checks[name] = str(residual)

    # Local holomorphic source jets, f != 0. Time jets obey f_t=kappa*f_ss and
    # (f_s)_t=kappa*f_sss. These operands determine the quotient derivatives.
    f = sp.Symbol("f", nonzero=True)
    f1, f2, f3 = sp.symbols("f_s f_ss f_sss")
    kappa = sp.Symbol("kappa", real=True)
    u = -2*kappa*f1/f
    us = -2*kappa*(f2/f-f1**2/f**2)
    uss = -2*kappa*(f3/f-3*f1*f2/f**2+2*f1**3/f**3)
    ut = -2*kappa**2*(f3/f-f1*f2/f**2)
    zero("source_jet_burgers", ut+u*us-kappa*uss)

    # A local pole of u=-2 G_s/G at a simple zero. The double-pole coefficient of
    # u_t+u*u_s-u_ss is 2*(regular_part - zero_velocity).
    q, b0, b1, b2, zdot = sp.symbols("q b0 b1 b2 z_dot")
    pole = -2/q+b0+b1*q+b2*q**2
    transport_residual = -2*zdot/q**2 + pole*sp.diff(pole,q)-sp.diff(pole,q,2)
    double_pole = sp.expand(transport_residual).coeff(q,-2)
    zero("pole_motion_is_regular_current", double_pole-2*(b0-zdot))

    # Actual entire polynomial heat source with a four-member reflected/conjugate orbit.
    s, t = sp.symbols("s t")
    d, y = sp.symbols("d y", positive=True)
    z = s-sp.Rational(1,2)
    p = z**4-2*(d**2-y**2)*z**2+(d**2+y**2)**2
    G = p+t*sp.diff(p,s,2)+t**2*sp.diff(p,s,4)/2
    zero("polynomial_source_heat", sp.diff(G,t)-sp.diff(G,s,2))
    polynomial_u = -2*sp.diff(G,s)/G
    zero("polynomial_source_burgers", sp.diff(polynomial_u,t)
         +polynomial_u*sp.diff(polynomial_u,s)-sp.diff(polynomial_u,s,2))
    root = sp.Rational(1,2)+d+sp.I*y
    zero("quartet_member_is_source_zero", G.subs({t:0,s:root}))
    velocity = -sp.diff(G,s,2).subs({t:0,s:root})/sp.diff(G,s).subs({t:0,s:root})
    zero("quartet_velocity", velocity-(-1/d+sp.I/y-1/(d+sp.I*y)))
    normal = -1/d-d/(d**2+y**2)
    tangent = 1/y+y/(d**2+y**2)
    zero("normal_and_tangent_current", velocity-normal-sp.I*tangent)

    # q=s-b(t), U(t,q)=u(t,q+b(t))-b'(t). No zero or datum is erased.
    bp, bpp = sp.symbols("b_prime b_second")
    relative_residual = (ut+bp*us-bpp)+(u-bp)*us-kappa*uss
    zero("moving_receiver_inertial_source", relative_residual+bpp)

    # A moving normal chart r=L*d changes coordinates and metric together.
    L = sp.Symbol("L", nonzero=True)
    Ldot, delta, delta_dot = sp.symbols("L_dot delta delta_dot")
    r, rdot = L*delta, Ldot*delta+L*delta_dot
    zero("normalized_gap", r**2/L**2-delta**2)
    zero("normalized_gap_rate", 2*r*rdot/L**2-2*Ldot*r**2/L**3-2*delta*delta_dot)

    # A moving capacitive membrane between two field potentials. Current is oriented
    # from minus to plus. C and its rate include the admitted geometry/material change.
    C, Cdot, V, Vdot, conductance = sp.symbols("C C_dot V V_dot conductance", real=True)
    charge_rate = C*Vdot+Cdot*V
    current = charge_rate+conductance*V
    energy_rate = C*V*Vdot+Cdot*V**2/2
    zero("moving_plate_power", V*current-energy_rate-conductance*V**2-Cdot*V**2/2)
    omitted = sp.expand(charge_rate-C*Vdot)
    assert omitted.subs({Cdot:1,V:1}) == 1

    result = {
        "arithmetic": "SymPy exact symbolic rational/algebraic differential identities",
        "scope": "source-qualified exterior audit; polynomial quartet is not xi",
        "checks": checks,
        "heat_source": str(G),
        "quartet_initial_member": str(root),
        "normal_velocity": str(normal),
        "tangential_velocity": str(tangent),
        "moving_burgers_force": str(-bpp),
        "omitted_capacitance_current": str(omitted),
        "moving_plate_power_exchange": str(Cdot*V**2/2),
        "elapsed_microseconds": (perf_counter_ns()-started)//1000,
    }
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"checks":len(checks),"output":str(args.output),"elapsed_microseconds":result["elapsed_microseconds"]}))


if __name__ == "__main__":
    main()
