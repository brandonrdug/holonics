#!/usr/bin/env python3
"""Cold experiment for contact through retained junction output, never a production learner.

The source projection is the first 4N real coordinates of an earlier complete junction outgoing
report. Raw phase/relation sources remain a separate receiver. This proposes a changed contact law;
it is not a new representation of the existing raw-source moment.
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
# The historical local reference is named inspect.py. Load it by its explicit file path below;
# keep it from shadowing stdlib inspect when argparse imports its formatting dependencies.
sys.path = [entry for entry in sys.path if Path(entry).resolve() != HERE]
import argparse

spec = importlib.util.spec_from_file_location('enclosure', HERE / 'enclosure.py')
if spec is None or spec.loader is None:
    raise RuntimeError('missing existing enclosure observer')
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)
p = e.reference
D = 96
SOURCE = 64


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def exact_states(lineages, fields, arrivals, count):
    contacts = []
    states = []
    prefix = [Q(0)] * D
    for at, (lineage, field, arrived) in enumerate(zip(lineages[:count], fields, arrivals)):
        source = lineage['received_from']
        if source is not None:
            d = p.complexify(states[source]['out'][:SOURCE]) + [p.zscale(v, Q(-1)) for v in arrived]
            contacts.append((d, p.zzero(), prefix[:]))
        receipt, contacts, v = p.passive_step(field, contacts)
        u = p.realify(field) + [Q(0)] * (D - SOURCE)
        out = p.sub_vectors(v, u)
        h = p.condensed_h(contacts) if contacts else [Q(0)] * D
        prefix = p.add_vectors(prefix, p.scale_vector(v, Q(-1 if at % 2 else 1)))
        matrix = p.matrix_from_contacts([p.contact_vectors(d) for d, _, _ in contacts], D)
        states.append({'v': v, 'out': out, 'h': h, 'prefix': prefix[:], 'matrix': matrix,
                       'contacts': contacts[:], 'receipt': receipt})
        print(json.dumps({'exact_anchor_completed': at + 1,
                          'maximum_reduced_denominator_bits': max(v.denominator.bit_length() for v in out)}), flush=True)
    return states


def ldlt(a_scaled, rhs, grain):
    """Integer LDL with A already in grid quanta. S is numeric precision, never dimension."""
    scale = 1 << grain
    lower = [[0] * D for _ in range(D)]
    diagonal = [0] * D
    maximum = 0
    for k in range(D):
        correction = 0
        for j in range(k):
            pair = e.product_shift_zero(lower[k][j], lower[k][j], grain)
            maximum = max(maximum, e.bits(lower[k][j] * lower[k][j]), e.bits(pair * diagonal[j]))
            correction += e.product_shift_zero(pair, diagonal[j], grain)
        diagonal[k] = a_scaled[k][k] - correction
        if diagonal[k] <= 0:
            raise ValueError(f'non-positive numerical LDL pivot {k}')
        for i in range(k + 1, D):
            correction = 0
            for j in range(k):
                pair = e.product_shift_zero(lower[i][j], lower[k][j], grain)
                maximum = max(maximum, e.bits(lower[i][j] * lower[k][j]), e.bits(pair * diagonal[j]))
                correction += e.product_shift_zero(pair, diagonal[j], grain)
            numerator = a_scaled[i][k] - correction
            maximum = max(maximum, e.bits(numerator * scale))
            lower[i][k] = e.scaled_div_zero(numerator, diagonal[k], grain)
    y = rhs[:]
    for i in range(D):
        for j in range(i):
            maximum = max(maximum, e.bits(lower[i][j] * y[j]))
            y[i] -= e.product_shift_zero(lower[i][j], y[j], grain)
    v = [e.scaled_div_zero(y[i], diagonal[i], grain) for i in range(D)]
    for i in range(D - 1, -1, -1):
        for j in range(i + 1, D):
            maximum = max(maximum, e.bits(lower[j][i] * v[j]))
            v[i] -= e.product_shift_zero(lower[j][i], v[j], grain)
    return v, maximum


def trial(lineages, fields, arrivals, grain, anchors):
    scale = 1 << grain
    covariance = [[0] * D for _ in range(D)]
    h = [0] * D
    prefix = [0] * D
    E_c = E_h = E_prefix = 0
    history = []
    steps = []
    checks = {key: 0 for key in ('potential', 'outgoing', 'held', 'prefix', 'covariance')}
    refusal = None
    for at, (lineage, field, arrived) in enumerate(zip(lineages, fields, arrivals)):
        source = lineage['received_from']
        next_covariance = [row[:] for row in covariance]
        next_E_c = E_c
        moment_rounding_l1_numerator = 0
        if source is not None:
            d = history[source]['out'][:SOURCE] + [-v * scale for v in e.integer_raw(arrived)]
            E_d = history[source]['E_out']
            jd = e.jrotate(d)
            for i in range(D):
                for j in range(D):
                    numerator = d[i] * d[j] + jd[i] * jd[j]
                    rounded = e.trunc_div(numerator, scale)
                    next_covariance[i][j] += rounded
                    moment_rounding_l1_numerator += abs(numerator - rounded * scale)
            # Realification is isometric for Hermitian operators. The coefficient L1 norm
            # bounds ||d_center||2; no extra realification dimension factor is needed here.
            next_E_c += ceil_div(2 * e.l1(d) * E_d + E_d * E_d, scale)
            next_E_c += ceil_div(moment_rounding_l1_numerator, scale)
        u = [value * scale for value in e.integer_raw(field)] + [0] * (D - SOURCE)
        rhs = [2 * (u[i] + h[i]) for i in range(D)]
        a_scaled = [[next_covariance[i][j] + (scale if i == j else 0)
                     for j in range(D)] for i in range(D)]
        try:
            v, product_bits = ldlt(a_scaled, rhs, grain)
        except ValueError as error:
            refusal = {'occurrence': at, 'reason': str(error)}
            break
        # Exact signed residual of the numerical operator is retained as a source expression.
        residual_numerator = [sum(a_scaled[i][j] * v[j] for j in range(D)) - scale * rhs[i]
                              for i in range(D)]
        R_center = ceil_div(e.l1(residual_numerator), scale)
        R_operator = ceil_div(next_E_c * e.l1(v), scale)
        R = R_center + R_operator
        E_v = 2 * E_h + R
        E_out = 2 * E_h + R
        E_hnext = E_h + R
        E_pnext = E_prefix + E_v
        out = [v[i] - u[i] for i in range(D)]
        hnext = [2 * u[i] + h[i] - v[i] for i in range(D)]
        pnext = [prefix[i] + (-1 if at % 2 else 1) * v[i] for i in range(D)]
        candidate = {'occurrence': at, 'received_from': source, 'E_c': next_E_c,
                     'E_v': E_v, 'E_out': E_out, 'E_h': E_hnext, 'E_prefix': E_pnext,
                     'R_center': R_center, 'R_operator': R_operator,
                     'outgoing_center_l1': e.l1(out), 'maximum_solver_product_bits': product_bits}
        if at < len(anchors):
            anchor = anchors[at]
            for key, exact, center, radius in (
                ('potential', anchor['v'], v, E_v), ('outgoing', anchor['out'], out, E_out),
                ('held', anchor['h'], hnext, E_hnext), ('prefix', anchor['prefix'], pnext, E_pnext)):
                if not e.sphere_contains(exact, center, radius, scale):
                    raise ValueError(f'{key} anchor containment failed at {at}')
                checks[key] += 1
            # Frobenius containment implies operator containment. This checks the conservative
            # bound used by this candidate against the full exact evolving moment.
            delta = [anchor['matrix'][i][j] - Q(a_scaled[i][j], scale)
                     for i in range(D) for j in range(D)]
            if sum((x*x for x in delta), Q(0)) > Q(next_E_c * next_E_c, scale * scale):
                raise ValueError(f'covariance anchor containment failed at {at}')
            checks['covariance'] += 1
        candidate['represented_outgoing_ball_contains_zero'] = sum(v*v for v in out) <= E_out * E_out
        candidate['radius_bits'] = max(e.bits(x) for x in (next_E_c, E_v, E_out, E_hnext, E_pnext))
        steps.append(candidate)
        if candidate['radius_bits'] > 127 or product_bits > 255:
            refusal = {'occurrence': at, 'reason': 'candidate signed-wide report or signed-256 product carrier',
                       'radius_bits': candidate['radius_bits'], 'product_bits': product_bits}
            break
        covariance, E_c, h, E_h, prefix, E_prefix = next_covariance, next_E_c, hnext, E_hnext, pnext, E_pnext
        history.append({'out': out, 'E_out': E_out})
    return {'fractional_bits': grain, 'accepted_occurrences': len(history), 'refusal': refusal,
            'exact_anchor_checks': checks, 'steps': steps,
            'first_ball_containing_zero': next((s['occurrence'] for s in steps if s['represented_outgoing_ball_contains_zero']), None)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report', type=Path)
    parser.add_argument('--occurrences', type=int, required=True)
    parser.add_argument('--exact-anchors', type=int, required=True)
    parser.add_argument('--precisions', type=int, nargs='+', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    if args.occurrences <= 0 or not 0 <= args.exact_anchors <= args.occurrences:
        raise ValueError('invalid declared observation aperture')
    if any(not 1 <= g <= 120 for g in args.precisions):
        raise ValueError('fractional precision is outside the candidate report chart')
    lineages, fields, arrivals = e.fields_from_report(report, args.occurrences)
    if len(lineages) != args.occurrences or any(l.get('frame') != 0 for l in lineages):
        raise ValueError('this experiment requires the full requested identity-frame material slice')
    if any(len(f) != SOURCE // 2 for f in fields):
        raise ValueError('this experiment requires the full 96-real-coordinate material field')
    anchors = exact_states(lineages, fields, arrivals, args.exact_anchors)
    result = {'truth_status': 'established-bounded', 'evidence_tags': ['computational-witness'],
              'candidate': 'paired contact uses the prior junction outgoing source projection',
              'carrier_real_dimension': D, 'requested_occurrences': args.occurrences,
              'exact_anchor_aperture': args.exact_anchors,
              'native_model_or_update_executed': False,
              'trials': [trial(lineages, fields, arrivals, g, anchors) for g in args.precisions]}
    with os.fdopen(os.open(args.output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600), 'w') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print(json.dumps({'published': str(args.output), 'trials': [
        {k: t[k] for k in ('fractional_bits', 'accepted_occurrences', 'refusal', 'exact_anchor_checks', 'first_ball_containing_zero')}
        for t in result['trials']]}), flush=True)


if __name__ == '__main__':
    main()
