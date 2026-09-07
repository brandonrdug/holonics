#!/usr/bin/env python3
"""Full-root residual certificates for the optional balanced numerical factorization.

The candidate still has 108 real coordinates. No centre is treated as the exact current, and
this observer does not execute the native model or grade the repeated text as useful.
"""
import importlib.util
import json
import os
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('text_return_inspection',HERE/'inspect_text_return.py')
if spec is None or spec.loader is None: raise RuntimeError('missing text-return inspector')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
D,N,STRIDE=b.D,b.N,b.STRIDE


def balanced(values):
    at=lambda bank,port:4*port+2*bank if bank<2 else 4*N+2*port
    for bank in range(3):
        for plane in range(2):
            expected=values[at(bank,0)+plane]+values[at(bank,1)+plane]
            if any(values[at(bank,2*bit)+plane]+values[at(bank,2*bit+1)+plane]!=expected for bit in range(1,N//2)):
                return False
    return True


def inspect(report,earlier):
    if report.get('junction_solver')!='balanced-pairs' or not report.get('all_currents_requested'):
        raise ValueError('the report does not carry the requested balanced-policy full current history')
    result=b.compare(report,earlier,require_identical_body=False)
    lineages=report['body']['lineage']
    history=report.get('junction_history',[])
    if len(history)!=len(lineages): raise ValueError('missing full native current history')
    covariance=[[0]*D for _ in range(D)]
    source_fields=[]
    previous_input=[0]*N
    h=prefix=[0]*D
    e_h=e_prefix=0
    scale=1 << report['fractional_bits']
    counts={name:0 for name in ('root_sections','source_centres','full_oriented_residuals','centre_recurrences','radii','balanced_root_fields')}
    for at,(lineage,entry) in enumerate(zip(lineages,history)):
        if entry['occurrence']!=at: raise ValueError('current chronology mismatch')
        _,incoming=b.input_code(lineage)
        raw=[v for a,c in zip(previous_input,incoming) for v in (a,0,c,0)]
        source_fields.append(raw)
        source=lineage['received_from']
        if source is not None:
            d=source_fields[source]+[-v for x in incoming for v in (x,0)]
            jd=[v for i in range(0,D,2) for v in (-d[i+1],d[i])]
            for vector in (d,jd):
                support=[(i,x) for i,x in enumerate(vector) if x]
                for i,x in support:
                    for j,y in support: covariance[i][j]+=x*y
        parts=b.unpack(entry['junction'])
        v,out,new_h,new_prefix,u,residual=parts
        counts['root_sections']+=1
        expected_u=[x*scale for x in raw]+[0]*(2*N)
        if u[:D]!=expected_u or u[D]!=0: raise ValueError(f'source centre mismatch at {at}')
        counts['source_centres']+=1
        expected_r=[v[i]+sum(covariance[i][j]*v[j] for j in range(D))-2*(u[i]+h[i]) for i in range(D)]
        if residual[:D]!=expected_r or residual[D]!=1: raise ValueError(f'full root residual mismatch at {at}')
        counts['full_oriented_residuals']+=1
        if out[:D]!=[v[i]-u[i] for i in range(D)] or new_h[:D]!=[2*u[i]+h[i]-v[i] for i in range(D)] or new_prefix[:D]!=[prefix[i]+(-1 if at%2 else 1)*v[i] for i in range(D)]:
            raise ValueError(f'centre recurrence mismatch at {at}')
        counts['centre_recurrences']+=1
        radius=sum(abs(x) for x in expected_r)
        if (v[D],out[D],new_h[D],new_prefix[D])!=(2*e_h+radius,2*e_h+radius,e_h+radius,e_prefix+2*e_h+radius):
            raise ValueError(f'current radius mismatch at {at}')
        counts['radii']+=1
        if all(balanced(values) for values in (v,out,new_h,new_prefix,u)):
            counts['balanced_root_fields']+=1
        else: raise ValueError(f'numerical root field left the declared balanced range at {at}')
        h,prefix=new_h[:D],new_prefix[:D]
        e_h,e_prefix=new_h[D],new_prefix[D]
        previous_input=incoming
    result['full_root_certificate_checks']=counts
    result['root_real_dimension']=D
    result['factor_coordinates_per_complex_component']=3*(N//2+1)
    result['exact_point_comparison_claim']=False
    endpoints=[part['native_until']-1 for record in report['development_records'] for part in record['parts']]
    source_collisions=[]
    for position,a in enumerate(endpoints):
        for other in endpoints[position+1:]:
            if source_fields[a] != source_fields[other]: continue
            left=b.unpack(history[a]['junction'])[1]
            right=b.unpack(history[other]['junction'])[1]
            radius_squared=(left[D]+right[D])**2
            source_collisions.append({'first':a,'second':other,'equal_complete_raw_source':True,
                'disjoint_complete_coupled_outgoing_balls':sum((x-y)**2 for x,y in zip(left[:D],right[:D]))>radius_squared,
                'disjoint_coupled_source_projection_balls':sum((x-y)**2 for x,y in zip(left[:4*N],right[:4*N]))>radius_squared})
    result['equal_raw_endpoint_distinctions']=source_collisions
    return result


def main():
    if len(sys.argv)!=5 or sys.argv[3]!='--output': raise SystemExit('usage: inspect_balanced_text_return.py REPORT EARLIER --output NEW.json')
    result=inspect(json.loads(Path(sys.argv[1]).read_text()),json.loads(Path(sys.argv[2]).read_text()))
    with os.fdopen(os.open(sys.argv[4],os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as out:
        json.dump(result,out,indent=2);out.write('\n')
    print(json.dumps(result))


if __name__=='__main__': main()
