#!/usr/bin/env python3
"""Checks, by quadrature and by fractions, the charts in which 8 pi stands, each as its own integral.

    python3 eight_pi.py

Printed, each beside 8 pi = 25.132741...:

  SPHERE     the curvature a closed surface of the sphere's kind owes, 2 pi chi with chi = 2 (4 pi), and twelve corners of a
             closed mesh of hexagons each owing pi / 3;
  POINT      the flux of grad(lap r) through a sphere about a point in three dimensions, where lap r = (d - 1) / r: the constant
             under a point force in a slow viscous fluid;
  PLANE      the mass at which a self-attracting cloud in the plane stops spreading: d/dt of its second moment is
             2 d M - M^2 / (2 pi) at d = 2, zero at M = 8 pi; and the area of the bubble exp(u) = 8 / (1 + r^2)^2 that solves
             -lap u = exp(u) there;
  HORIZON    the period in imaginary time at which the cone at a horizon of mass M closes with no tip: 2 pi / kappa with
             kappa = 1 / (4 M);
  EINSTEIN   the coupling that gives lap phi = 4 pi rho in D space-time dimensions, 4 pi (D - 2) / (D - 3), beside the count
             D - 2 of directions across a ray.

A ruler of arithmetic. It holds no law of the engine.
"""
import math
from fractions import Fraction

EIGHT_PI = 8 * math.pi


def simpson(f, a, b, n=200000):
    h = (b - a) / n
    return (f(a) + f(b) + 4 * sum(f(a + (2 * i - 1) * h) for i in range(1, n // 2 + 1)) + 2 * sum(f(a + 2 * i * h) for i in range(1, n // 2))) * h / 3


def main():
    print(f"EIGHT_PI {EIGHT_PI:.9f}")
    print(f"SPHERE two_pi_chi={2 * math.pi * 2:.9f} share_of_eight_pi={Fraction(1, 2)} twelve_corners_of_pi_over_3={12 * math.pi / 3:.9f}")
    # lap r = (d - 1) / r; the flux of grad((d - 1) / r) through a sphere of radius R in d = 3 is -(d - 1) / R^2 times 4 pi R^2.
    d = 3
    flux = -(d - 1) * 4 * math.pi
    print(f"POINT d={d} lap_r_times_r={d - 1} flux_of_grad_lap_r={flux:.9f} ratio_to_eight_pi={flux / EIGHT_PI:+.6f}")
    # numeric check of lap r = 2 / r at r = 1.7 by finite differences on the radial Laplacian f'' + (d - 1) f' / r
    r, e = 1.7, 1e-4
    lap = ((r + e) - 2 * r + (r - e)) / e ** 2 + (d - 1) * ((r + e) - (r - e)) / (2 * e) / r
    print(f"POINT lap_r_at_1.7={lap:.6f} two_over_r={2 / r:.6f}")
    # a cloud in the plane: d/dt int |x|^2 rho = 2 d M - M^2 / (2 pi); zero at M = 4 pi d = 8 pi at d = 2.
    d = 2
    m_star = 2 * d * 2 * math.pi
    print(f"PLANE d={d} mass_where_spreading_stops={m_star:.9f} ratio_to_eight_pi={m_star / EIGHT_PI:.6f}")
    # the bubble: int_0^inf 8 / (1 + r^2)^2 * 2 pi r dr, by the substitution r = tan(t)
    area = simpson(lambda t: 8 * math.cos(t) ** 4 * 2 * math.pi * math.tan(t) / math.cos(t) ** 2, 0.0, math.pi / 2 - 1e-9)
    print(f"PLANE bubble_area={area:.6f} ratio_to_eight_pi={area / EIGHT_PI:.6f} its_curvature=1/2 curvature_times_area={area / 2:.6f} (4 pi = {4 * math.pi:.6f})")
    # -lap u = exp(u) for u = ln 8 - 2 ln(1 + r^2), checked at r = 0.9 by the radial Laplacian in the plane
    u = lambda x: math.log(8) - 2 * math.log(1 + x * x)
    r, e = 0.9, 1e-4
    lap = (u(r + e) - 2 * u(r) + u(r - e)) / e ** 2 + (u(r + e) - u(r - e)) / (2 * e) / r
    print(f"PLANE minus_lap_u_at_0.9={-lap:.6f} exp_u={math.exp(u(r)):.6f}")
    kappa = Fraction(1, 4)
    print(f"HORIZON kappa_times_M={kappa} period_over_M=2 pi / kappa={2 * math.pi / float(kappa):.9f} ratio_to_eight_pi={2 * math.pi / float(kappa) / EIGHT_PI:.6f}")
    for big_d in (4, 5, 6, 11):
        c = Fraction(big_d - 2, big_d - 3)
        print(f"EINSTEIN D={big_d} coupling_over_4_pi={c} directions_across_a_ray={big_d - 2} states_of_light={big_d - 2} states_of_gravity={Fraction((big_d - 2) * (big_d - 1), 2) - 1}")


main()
