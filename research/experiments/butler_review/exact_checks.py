"""Independent rational checks of explicitly stated source equations.

No Butler/SpiralOS code is imported or executed. General derivations and source scopes are
in the companion report; finite evaluations here witness the stated counterexamples.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
import json


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def sub(a, b):
    return [[a[i][j] - b[i][j] for j in range(2)] for i in range(2)]


def transpose(a):
    return [list(v) for v in zip(*a)]


def metric_derivative(gamma):
    return [[-gamma[i][j] - gamma[j][i] for j in range(2)] for i in range(2)]


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def checks():
    # HC I / II displayed connection, tau=1, coordinates (t,x), g=I.
    gt = [[Q(0), Q(0)], [Q(0), Q(1, 2)]]
    gx = [[Q(0), Q(0)], [Q(-1, 2), Q(0)]]
    curvature = sub(mul(gt, gx), mul(gx, gt))
    nonmetric = metric_derivative(gt)
    assert curvature[1][0] == Q(-1, 4)
    assert nonmetric[1][1] == -1

    # A consistent constant, metric-compatible, affine-flat replacement with torsion.
    rt = [[Q(0), Q(0)], [Q(0), Q(0)]]
    rx = [[Q(0), Q(1)], [Q(-1), Q(0)]]
    zero = [[Q(0), Q(0)], [Q(0), Q(0)]]
    assert metric_derivative(rt) == metric_derivative(rx) == zero
    assert sub(mul(rt, rx), mul(rx, rt)) == zero
    torsion_x_tx = rt[1][1] - rx[1][0]
    divergence_constant_phi = rt[0][0] + rx[1][0]  # Phi=(1,0).
    hse = divergence_constant_phi + torsion_x_tx  # dual chi with half antisymmetry; R_e=0.
    assert torsion_x_tx == 1 and hse == 0

    eta, lipschitz = Q(1, 2), Q(1)
    claimed_c = eta * (1 - lipschitz * eta / 2)
    # HC III theorem allows lambda=0, a closed convex interval, and these smooth task losses.
    boundary = {'x': Q(1), 'gradient': Q(-1), 'next': Q(1), 'before_loss': Q(0),
                'after_loss': Q(0), 'projected_positive_gradient': Q(-1),
                'claimed_upper_loss': -claimed_c}
    assert boundary['after_loss'] > boundary['claimed_upper_loss']
    x = Q(1, 8)
    next_x = max(Q(0), min(Q(1), x - eta))
    interior = {'x': x, 'gradient': Q(1), 'next': next_x, 'before_loss': x,
                'after_loss': next_x, 'claimed_upper_loss': x - claimed_c,
                'gradient_mapping': (x - next_x) / eta,
                'correct_upper_loss': x - (1 / eta - lipschitz / 2) * (next_x - x) ** 2}
    assert interior['after_loss'] > interior['claimed_upper_loss']
    assert interior['after_loss'] <= interior['correct_upper_loss']

    # Golden mode phi^2=phi+1, phi>1 implies phi>8/5. Integral comparison bounds zeta(s).
    lo = Q(8, 5)
    tails = {str(n): lo ** (-n) / (lo - 1) * (1 + 1 / (lo ** (n + 1) - 1))
             for n in [4, 8, 16, 32, 64]}
    assert all(v > 0 for v in tails.values())
    # CI II's actual eight-row table ties phase to perspective; HC I's free product does not.
    octants = [v for v in product([0, 1], repeat=4) if v[2] == v[3]]
    assert len(octants) == 8
    assert all(tuple(1 - x for x in v) in octants for v in octants)
    # Endpoint admissibility in the category note is not automatically composition-closed.
    adjacent = lambda a, b: abs(b - a) <= 1
    assert adjacent(0, 1) and adjacent(1, 2) and not adjacent(0, 2)
    return {'scope': 'independent exact arithmetic; not execution of the external package',
            'connection_convention': 'nabla_mu v^lambda = partial_mu v^lambda + Gamma^lambda_mu_nu v^nu',
            'original_connection': {'Gamma_t': gt, 'Gamma_x': gx,
                'nabla_t_g': nonmetric, 'R_tx': curvature},
            'repaired_connection': {'Gamma_t': rt, 'Gamma_x': rx, 'torsion_x_tx': torsion_x_tx,
                'divergence_Phi_1_0': divergence_constant_phi, 'HSE': hse},
            'projected_descent': {'eta': eta, 'L': lipschitz, 'claimed_c': claimed_c,
                'boundary_counterexample': boundary, 'interior_counterexample': interior},
            'four_binary_factors_cardinality': 2 ** 4,
            'CI_II_correlated_octants': {'count': len(octants), 'phase_equals_perspective': octants},
            'endpoint_predicate_counterexample': {'0_to_1': True, '1_to_2': True,
                '0_to_2': False, 'repair': 'retain the composite path (0,1,2) as a distinct arrow'},
            'golden_weighted_zeta_tail_upper': tails}


if __name__ == '__main__':
    target = Path(__file__).with_name('exact_checks.json')
    target.write_text(json.dumps(encode(checks()), indent=2) + '\n')
    print(target)
