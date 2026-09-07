#!/usr/bin/env python3
"""Cold centre-trajectory comparison for the contextual-source candidate.

This evaluates numerical centres at two declared precisions. Agreement is not an exact enclosure,
model return, or permission to use a centre as a productive source. No native model is executed.
"""
import importlib.util
import json
import os
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path = [entry for entry in sys.path if Path(entry).resolve() != HERE]
import argparse

spec = importlib.util.spec_from_file_location('contextual_source_reference', HERE / 'contextual_source.py')
if spec is None or spec.loader is None:
    raise RuntimeError('missing contextual source reference')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
e = c.e


def trajectory(lineages, fields, arrivals, grain):
    dimension = 2 * (len(fields[0]) + len(arrivals[0]))
    source_width = 2 * len(fields[0])
    scale = 1 << grain
    covariance = [[0] * dimension for _ in range(dimension)]
    held = [0] * dimension
    history = []
    max_residual = 0
    for at, (lineage, raw, arrived) in enumerate(zip(lineages, fields, arrivals)):
        source = lineage['received_from']
        if source is not None:
            if not 0 <= source < at:
                raise ValueError('source is not actual earlier standing')
            d = history[source]['out'][:source_width] + [-v * scale for v in e.integer_raw(arrived)]
            jd = e.jrotate(d)
            for i in range(dimension):
                for j in range(dimension):
                    covariance[i][j] += e.trunc_div(d[i] * d[j] + jd[i] * jd[j], scale)
        u = [value * scale for value in e.integer_raw(raw)] + [0] * (dimension - source_width)
        rhs = [2 * (u[i] + held[i]) for i in range(dimension)]
        matrix = [[covariance[i][j] + (scale if i == j else 0) for j in range(dimension)] for i in range(dimension)]
        v, product_bits = c.ldlt(matrix, rhs, grain)
        residual = [sum(matrix[i][j] * v[j] for j in range(dimension)) - scale * rhs[i] for i in range(dimension)]
        max_residual = max(max_residual, c.ceil_div(e.l1(residual), scale))
        out = [v[i] - u[i] for i in range(dimension)]
        held = [2*u[i] + held[i] - v[i] for i in range(dimension)]
        history.append({'v': v, 'out': out, 'held': held, 'product_bits': product_bits})
        if (at+1) % 25 == 0:
            print(json.dumps({'precision': grain, 'centre_occurrences': at+1}), flush=True)
    return history, max_residual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report', type=Path)
    parser.add_argument('--occurrences', type=int, required=True)
    parser.add_argument('--precisions', nargs=2, type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not 0 < args.precisions[0] < args.precisions[1] or args.occurrences <= 0:
        raise ValueError('declare two increasing positive precisions and an actual input aperture')
    report = json.loads(args.report.read_text())
    lineages, fields, arrivals = e.fields_from_report(report, args.occurrences)
    if len(lineages) != args.occurrences or any(l['frame'] != 0 for l in lineages):
        raise ValueError('this cold study requires the complete requested identity-frame material')
    if 'development_native_until' in report and args.occurrences > report['development_native_until']:
        raise ValueError('do not substitute the earlier model self-emissions for this candidate material')
    start = time.monotonic()
    low, residual_low = trajectory(lineages, fields, arrivals, args.precisions[0])
    high, residual_high = trajectory(lineages, fields, arrivals, args.precisions[1])
    shift = args.precisions[1] - args.precisions[0]
    scale = 1 << args.precisions[1]
    values = []
    for at, (a, b) in enumerate(zip(low, high)):
        differences = {name: sum(abs((x << shift) - y) for x, y in zip(a[name], b[name]))
                       for name in ('v', 'out', 'held')}
        values.append({'occurrence': at, 'l1_difference_numerators': differences})
    maxima = {name: max(v['l1_difference_numerators'][name] for v in values) for name in ('v','out','held')}
    result = {'truth_status': 'established-bounded', 'evidence_tags': ['computational-witness'],
              'carrier_real_dimension': len(low[0]['out']), 'precisions': args.precisions,
              'occurrences': len(lineages), 'common_difference_denominator': str(scale),
              'maximum_l1_differences': {k: str(Q(v, scale)) for k, v in maxima.items()},
              'maximum_l1_difference_numerator_bits': {k:v.bit_length() for k,v in maxima.items()},
              'maximum_local_residual_quanta': [residual_low,residual_high],
              'exact_point_or_enclosure_claim': False, 'native_model_or_update_executed': False,
              'elapsed_seconds':time.monotonic()-start, 'steps':values}
    with os.fdopen(os.open(args.output, os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as stream:
        json.dump(result,stream,indent=2);stream.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k!='steps'}),flush=True)


if __name__ == '__main__':
    main()
