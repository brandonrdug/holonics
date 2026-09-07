#!/usr/bin/env python3
"""Exact-range factorization and cold numerical comparison for contextual source transport.

The full root field is retained by an explicit injective decoder. This is not cropping the field,
a learned semantic classifier, or an exactness claim for a numerical centre trajectory.
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

spec = importlib.util.spec_from_file_location('source_precision_reference', HERE / 'compare_source_precision.py')
if spec is None or spec.loader is None:
    raise RuntimeError('missing centre trajectory reference')
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
c, e, p = f.c, f.e, f.c.p


def reduce_ports(real):
    if len(real) % 2:
        raise ValueError('an input pair is incomplete')
    sums = [real[i]+real[i+1] for i in range(0,len(real),2)]
    if any(value != sums[0] for value in sums):
        raise ValueError('the complete port field is outside the balanced chart')
    return [sums[0]] + list(real[1::2])


def lift_ports(values):
    return [part for right in values[1:] for part in (values[0]-right,right)]


def real_complex(values):
    if any(imaginary != 0 for _, imaginary in values):
        raise ValueError('this declared excitation chart has real root currents')
    return [real for real, _ in values]


def reduce_raw_source(field):
    return reduce_ports(real_complex(field[::2])) + reduce_ports(real_complex(field[1::2]))


def lift(values, bits):
    width = bits + 1
    source_out = lift_ports(values[:width])
    source_held = lift_ports(values[width:2*width])
    target = lift_ports(values[2*width:])
    return [component for a,b in zip(source_out,source_held) for component in (a,0,b,0)] + [component for a in target for component in (a,0)]


def reduce_full(values, bits):
    source_width = 8 * bits
    source = p.complexify(values[:source_width])
    target = p.complexify(values[source_width:])
    return reduce_raw_source(source) + reduce_ports(real_complex(target))


def metric(bits):
    width = bits + 1
    dimension = 3 * width
    g = [[0]*dimension for _ in range(dimension)]
    for bank in range(3):
        start = bank*width
        g[start][start] = bits
        for i in range(start+1,start+width):
            g[start][i] = g[i][start] = -1
            g[i][i] = 2
    return g


def matvec(matrix, vector):
    return [sum(a*b for a,b in zip(row,vector)) for row in matrix]


def exact_anchors(lineages, fields, arrivals, count, bits):
    dimension = 3*(bits+1)
    g = metric(bits)
    cov = [[Q(0)]*dimension for _ in range(dimension)]
    hred = [Q(0)]*dimension
    history, contacts = [], []
    full_width = len(lift([Q(0)]*dimension,bits))
    prefix = [Q(0)]*full_width
    for at,(lineage,raw,arrived) in enumerate(zip(lineages[:count],fields,arrivals)):
        source = lineage['received_from']
        if source is not None:
            difference = p.complexify(history[source]['out'][:8*bits]) + [p.zscale(v,Q(-1)) for v in arrived]
            contacts.append((difference,p.zzero(),prefix[:]))
            d = reduce_full(p.realify(difference),bits)
            covector = matvec(g,d)
            for i in range(dimension):
                for j in range(dimension): cov[i][j] += covector[i]*covector[j]
        receipt, contacts, v = p.passive_step(raw,contacts)
        u = p.realify(raw) + [Q(0)]*(4*bits)
        out = p.sub_vectors(v,u)
        h = p.condensed_h(contacts) if contacts else [Q(0)]*full_width
        vr, ur = reduce_full(v,bits), reduce_full(u,bits)
        if lift(vr,bits) != v or lift(reduce_full(out,bits),bits) != out or lift(reduce_full(h,bits),bits) != h:
            raise ValueError('exact source/current left the declared invariant subspace')
        lhs = matvec([[Q(g[i][j])+cov[i][j] for j in range(dimension)] for i in range(dimension)],vr)
        rhs = matvec(g,[2*(a+b) for a,b in zip(ur,hred)])
        if lhs != rhs:
            raise ValueError('the reduced metric system does not intertwine with the full current')
        hred = reduce_full(h,bits)
        prefix = p.add_vectors(prefix,p.scale_vector(v,Q(-1 if at%2 else 1)))
        history.append({'v':v,'out':out,'held':h})
    return history


def trajectory(lineages,fields,arrivals,grain,bits,unit_series=False):
    dimension = 3*(bits+1)
    source_width = 2*(bits+1)
    g = metric(bits)
    scale = 1 << grain
    covariance = [[0]*dimension for _ in range(dimension)]
    held = [0]*dimension
    history = []
    maximum_residual = 0
    for at,(lineage,raw,arrived) in enumerate(zip(lineages,fields,arrivals)):
        source = lineage['received_from']
        if source is not None:
            d = history[source]['out_red'][:source_width] + [-int(v*scale) for v in reduce_ports(real_complex(arrived))]
            covector = matvec(g,d)
            denominator = scale*scale + sum(a*b for a,b in zip(d,covector)) if unit_series else scale
            for i in range(dimension):
                for j in range(dimension):
                    numerator = covector[i]*covector[j]*(scale if unit_series else 1)
                    covariance[i][j] += e.trunc_div(numerator,denominator)
        u = [int(v*scale) for v in reduce_raw_source(raw)] + [0]*(bits+1)
        rhs = matvec(g,[2*(u[i]+held[i]) for i in range(dimension)])
        matrix = [[g[i][j]*scale+covariance[i][j] for j in range(dimension)] for i in range(dimension)]
        v,_ = c.ldlt(matrix,rhs,grain)
        residual = [a-scale*b for a,b in zip(matvec(matrix,v),rhs)]
        maximum_residual = max(maximum_residual,c.ceil_div(e.l1(residual),scale))
        out = [v[i]-u[i] for i in range(dimension)]
        held = [2*u[i]+held[i]-v[i] for i in range(dimension)]
        history.append({'v':lift(v,bits),'out':lift(out,bits),'held':lift(held,bits),'out_red':out})
        if (at+1)%100==0: print(json.dumps({'range_precision':grain,'centre_occurrences':at+1}),flush=True)
    return history,maximum_residual


def difference(a,b,low,high):
    shift = high-low
    return {name:sum(abs((x << shift)-y) for x,y in zip(a[name],b[name])) for name in ('v','out','held')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report',type=Path)
    parser.add_argument('--occurrences',type=int,required=True)
    parser.add_argument('--exact-anchors',type=int,required=True)
    parser.add_argument('--precisions',type=int,nargs=2,required=True)
    parser.add_argument('--compare-full',action='store_true')
    parser.add_argument('--unit-series',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    lineages,fields,arrivals = e.fields_from_report(report,args.occurrences)
    if len(lineages)!=args.occurrences or any(l['frame']!=0 for l in lineages):
        raise ValueError('the whole requested identity-frame material is required')
    if args.occurrences>report.get('development_native_until',len(lineages)):
        raise ValueError('candidate material must not include another model self-emissions')
    if len(arrivals[0])%2 or not 0<args.precisions[0]<args.precisions[1] or not 0<=args.exact_anchors<=args.occurrences:
        raise ValueError('invalid declared chart or observation aperture')
    bits = len(arrivals[0])//2
    start = time.monotonic()
    if args.unit_series and (args.compare_full or args.exact_anchors):
        raise ValueError('the existing exact/full comparison is for the unscreened law only')
    anchors = exact_anchors(lineages,fields,arrivals,args.exact_anchors,bits)
    low,lr = trajectory(lineages,fields,arrivals,args.precisions[0],bits,args.unit_series)
    high,hr = trajectory(lineages,fields,arrivals,args.precisions[1],bits,args.unit_series)
    steps = [dict(occurrence=at,l1_difference_numerators=difference(a,b,*args.precisions)) for at,(a,b) in enumerate(zip(low,high))]
    scale = 1 << args.precisions[1]
    maxima = {name:max(s['l1_difference_numerators'][name] for s in steps) for name in ('v','out','held')}
    full_difference = None
    if args.compare_full:
        full,_ = f.trajectory(lineages,fields,arrivals,args.precisions[1])
        full_difference = {name:str(Q(max(sum(abs(x-y) for x,y in zip(a[name],b[name])) for a,b in zip(full,high)),scale)) for name in ('v','out','held')}
    anchor_errors = []
    for grain,trajectory_values in zip(args.precisions,(low,high)):
        anchor_errors.append({name:str(max(sum(abs(Q(x,1 << grain)-y) for x,y in zip(s[name],exact[name])) for s,exact in zip(trajectory_values,anchors))) if anchors else None for name in ('v','out','held')})
    result = {'truth_status':'established-bounded','evidence_tags':['computational-witness'],
        'contact_law':'unit-series' if args.unit_series else 'unscreened',
        'root_real_dimension':len(low[0]['out']),'invariant_real_dimension':3*(bits+1),
        'precisions':args.precisions,'occurrences':len(lineages),'exact_intertwining_anchors':len(anchors),
        'maximum_l1_differences':{k:str(Q(v,scale)) for k,v in maxima.items()},
        'maximum_l1_difference_numerator_bits':{k:v.bit_length() for k,v in maxima.items()},
        'common_difference_denominator':str(scale),'full_vs_range_at_high_precision':full_difference,
        'maximum_exact_anchor_l1_errors':anchor_errors,'maximum_local_residual_quanta':[lr,hr],
        'exact_point_or_enclosure_claim_for_numeric_trajectory':False,'native_model_or_update_executed':False,
        'elapsed_seconds':time.monotonic()-start,'steps':steps}
    with os.fdopen(os.open(args.output,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as stream:
        json.dump(result,stream,indent=2);stream.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k!='steps'}),flush=True)


if __name__=='__main__': main()
