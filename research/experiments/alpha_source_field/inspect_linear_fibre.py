#!/usr/bin/env python3
"""Exact observer of a saved matched-unit field run; never a learner or native controller.

Reconstruct the branch source from the declared involutive matched junction, validate the saved
native source, exhibit a finite dependency with a nonzero returned target, and inspect the full
local Hermitian pair receiver. This reads a private report and emits mathematical testimony only.
"""
from fractions import Fraction as Q
import argparse
import json
from pathlib import Path
from math import gcd
from functools import reduce
import os


def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def phase(p): return (Q(p['real'],p['denominator']),Q(p['imaginary'],p['denominator']))
def dot(weights,rows): return [sum(w*row[j] for w,row in zip(weights,rows)) for j in range(len(rows[0]))]
def wire(v): return str(v.numerator) if v.denominator==1 else f'{v.numerator}/{v.denominator}'


def inspect(report):
    if report['profile']!='matched-unit-octet-excitation-native-field':
        raise ValueError('observer requires the declared matched-unit fixed chart')
    vertex=report['first_vertical_formation']
    if vertex is None: raise ValueError('no recorded vertical formation')
    last=vertex['native_occurrence']
    lineages=report['body']['lineage']
    nodes=len(lineages[0]['incoming']);held=[(Q(0),Q(0))]*nodes
    raw=[];quadratic=[];arrivals=[]
    for number,lineage in enumerate(lineages):
        if lineage['occurrence']!=number:raise ValueError('noncontiguous native chronology')
        if lineage.get('frame',0)!=0:raise ValueError('observer does not reconstruct a live rechart')
        incoming=list(map(phase,lineage['incoming']))
        # For unit/unit admittances and identity incidence: b_out=held, b_held=incoming.
        source=[];gram=[]
        for out,next_held in zip(held,incoming):
            source.extend((*out,*next_held))
            pair=mul((out[0],-out[1]),next_held)
            gram.extend((sum(x*x for x in out),*pair,sum(x*x for x in next_held)))
        raw.append(source);quadratic.append(gram);arrivals.append([x for p in incoming for x in p])
        held=incoming
    readbacks={vertex['source_occurrence']:vertex['paired_source']}
    readbacks.update(dict(report['body'].get('requested_sources',[])))
    if report['body']['last_source'] is not None:
        readbacks[len(lineages)-1]=report['body']['last_source']
    for source_at,section in readbacks.items():
        native=section['intervals'];den=native[4*nodes][0]
        assert den>0 and all(a==b for a,b in native)
        assert raw[source_at]==[Q(native[j][0],den) for j in range(4*nodes)]
    all_pairs=[(lineage['received_from'],j) for j,lineage in enumerate(lineages) if lineage['received_from'] is not None]
    pairs=[pair for pair in all_pairs if pair[1]<=last]
    xs=[raw[i] for i,j in pairs];ys=[arrivals[j] for i,j in pairs]
    qs=[quadratic[i] for i,j in pairs]
    n=len(pairs);basis={};witness=None
    # Rational source-only elimination. A certificate is checked afterward by direct products
    # against every original coordinate, independently of the native fraction-free row basis.
    for i,(source,target) in enumerate(zip(xs,ys)):
        x=source[:];y=target[:];c=[Q(j==i) for j in range(n)]
        for p,(bx,by,bc) in sorted(basis.items()):
            scale=x[p]
            x=[a-scale*b for a,b in zip(x,bx)]
            y=[a-scale*b for a,b in zip(y,by)]
            c=[a-scale*b for a,b in zip(c,bc)]
        pivot=next((p for p,v in enumerate(x) if v),None)
        if pivot is None:
            if any(y):witness=c;break
        else:
            scale=x[pivot]
            basis[pivot]=([v/scale for v in x],[v/scale for v in y],[v/scale for v in c])
    if witness is None:raise ValueError('saved first vertical formation has no independently found source dependency')
    common=1
    for v in witness:common=common*v.denominator//gcd(common,v.denominator)
    integers=[int(v*common) for v in witness]
    divisor=reduce(gcd,(abs(v) for v in integers),0)
    integers=[v//divisor for v in integers]
    source_residue=dot(integers,xs);target_residue=dot(integers,ys);higher=dot(integers,qs)
    assert not any(source_residue) and any(target_residue)
    basis_after=vertex['relation_after'];width=basis_after['width'];p=vertex['formed_pivot']
    native_row=[Q(v[0]) for v in basis_after['intervals'][p*width:(p+1)*width]]
    assert not any(native_row[:4*nodes])
    native_target=native_row[4*nodes:]
    at=next(j for j,v in enumerate(native_target) if v)
    ratio=target_residue[at]/native_target[at]
    assert [ratio*v for v in native_target]==target_residue
    # A second, stronger obstruction: equality of the actual local field, not just linear
    # dependence. Any deterministic receiver of that field alone has the same value twice.
    # The full retained chronology is still distinct; it has not been made operative by an ID.
    seen={};collision=None
    for source,receiving in all_pairs:
        key=tuple(raw[source])
        if key in seen:
            former_source,former_receiving=seen[key]
            if arrivals[former_receiving]!=arrivals[receiving]:
                a,b=former_source,source
                separation=None
                offset=0
                while a is not None and b is not None:
                    if raw[a]!=raw[b]:
                        separation={
                            'predecessor_steps':offset,
                            'source_occurrences':[a,b],
                            'complete_fields':[[wire(v) for v in raw[k]] for k in (a,b)],
                        }
                        break
                    a=lineages[a]['predecessor_state'];b=lineages[b]['predecessor_state']
                    offset+=1
                if separation is None and a!=b:
                    separation={'predecessor_steps':offset,'boundary_occurrences':[a,b]}
                assert separation is not None
                collision={
                    'source_occurrences':[former_source,source],
                    'receiving_occurrences':[former_receiving,receiving],
                    'identical_complete_source':[wire(v) for v in raw[source]],
                    'distinct_arrivals':[[wire(v) for v in arrivals[k]] for k in (former_receiving,receiving)],
                    'arriving_difference':[wire(b-a) for a,b in zip(arrivals[former_receiving],arrivals[receiving])],
                    'native_source_readbacks_verified':all(k in readbacks for k in (former_source,source)),
                    'separating_retained_history':separation,
                    'consequence':'No function of this local source field alone can equal both observed arriving fields; a polynomial lift of the same field cannot remove this collision.',
                    'limit':'The next exterior inputs differ; this is not a same-generator continuation or dynamic-condensation counterexample for the complete ecology.',
                }
                break
        else:seen[key]=(source,receiving)
    return {
        'truth_status':'counterexample','evidence_tags':['computational-witness'],
        'scope':'The fixed linear source chart does not determine one receiving field on these actual material observations; no general language impossibility follows.',
        'native_first_vertical_occurrence':last,'source_dimension':len(xs[0]),'target_dimension':len(ys[0]),
        'observation_pairs':[{'source':pairs[i][0],'receiving':pairs[i][1],'coefficient':str(v)} for i,v in enumerate(integers) if v],
        'source_combination':[wire(v) for v in source_residue],
        'returned_difference':[wire(v) for v in target_residue],
        'native_vertical_row_multiple':wire(ratio),
        'local_hermitian_receiver_combination':[wire(v) for v in higher],
        'local_hermitian_receiver_separates':any(higher),
        'higher_receiver_order':'per node: |out|^2, Re(conj(out)*held), Im(conj(out)*held), |held|^2',
        'source_reconstruction_matches_native':True,
        'verified_native_source_occurrences':sorted(readbacks),
        'identical_field_distinct_history':collision,
        'native_model_or_update_executed':False,
    }


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('report',type=Path);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();result=inspect(json.loads(a.report.read_text()))
    # Excitations and exact fields reconstruct private text; protect the witness from creation.
    fd=os.open(a.output,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
    with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ['native_first_vertical_occurrence','source_dimension','target_dimension','local_hermitian_receiver_separates','source_reconstruction_matches_native']}))

if __name__=='__main__':main()
