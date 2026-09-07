#!/usr/bin/env python3
"""Cold integer certificate for the complete-current native material return.

This evaluates retained numerical factors and error formulas. It executes no native model and
does not claim an exact physical coefficient reconstruction beyond the separate native controls.
"""
import importlib.util
import json
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

spec=importlib.util.spec_from_file_location('history_geometry',Path(__file__).with_name('current_history_source.py'))
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
Z=(0,0)
def ceildiv(a,b): return -(-a//b)
def trunc(a,b): return -(abs(a)//b) if a<0 else a//b
def norm(v):
    square=h.dot(v,v)[0];root=h.math.isqrt(square)
    return root+(root*root!=square)
def grid(v,scale): return [(trunc(a,scale),trunc(b,scale)) for a,b in v]
def rounding(v,scale): return sum(a%scale!=0 for x in v for a in x)
def bigint(value): return value[0]*sum(v<<(32*i) for i,v in enumerate(value[1]))
def rational(value): return Q(bigint(value[0]),bigint(value[1]))
def complex_q(value): return rational(value['real']),rational(value['imaginary'])
def apply(matrix,vector): return [h.sum_complex(h.mul(a,b) for a,b in zip(row,vector)) for row in matrix]
def error_bound(et,nt,source,scale,rounds):
    nx=norm(source['outgoing']+source['internal'])
    return ceildiv(et*(nx+source['radius']),scale)+ceildiv(nt*source['radius'],scale)+rounds


def inspect(report):
    if report.get('material_source')!='complete-current' or any(report.get(k) for k in ['native_error','development_error','prompt_error']):
        raise ValueError('complete-current material run did not return')
    lines=report['body']['lineage'];history=report['junction_history']
    if len(lines)!=len(history): raise ValueError('all native currents are required')
    n=len(lines[0]['incoming']);d=6*n;r=2*n;m=3*n;s=1<<report['fractional_bits'];s2=s*s;s3=s2*s
    bs=r+1;beta_at=12*bs;forward_at=beta_at+2*r;feature_at=forward_at+5*r;extra_at=feature_at+6*d+22
    geometry=h.PrefixGeometry(m);raw=[];previous=[Z]*n;before=[Z]*m;ep=0
    sources=[];betas=[];forwards=[];balls=[]
    M=[[Z]*m for _ in range(n)];A=[[Z]*m for _ in range(n)];a=[Z]*n;et=nt=0;tail_terms=0
    for at,(line,wire) in enumerate(zip(lines,history)):
        if line['occurrence']!=at or wire['occurrence']!=at or line['frame']!=0: raise ValueError('root frame or chronology mismatch')
        incoming=[]
        for v in line['incoming']:
            if v['denominator']!=1: raise ValueError('integral input certificate chart')
            incoming.append((v['real'],v['imaginary']))
        raw.append([v for x,y in zip(previous,incoming) for v in (x,y)])
        old=line['received_from']
        if old is not None: geometry.admit(at,raw[old]+[h.neg(v) for v in incoming],before,ep)
        jw=h.unpack(wire['junction']);js=d+1
        p=h.pairs(jw[js:js+d]);P=h.pairs(jw[3*js:3*js+d])
        source=geometry.source(at,p,P,jw[2*js-1],jw[4*js-1])
        points=wire['transport']['intervals']
        if len(points)!=extra_at+10 or any(x!=y for x,y in points): raise ValueError('complete report wire')
        h.check_native_source({'occurrence':at,'source':{'intervals':points[feature_at:extra_at]}},source,m,report['fractional_bits'])
        first=h.unpack({'intervals':points[:beta_at+2*r]})
        actual_balls=[(h.pairs(first[k*bs:k*bs+r]),first[k*bs+r]) for k in range(6)]
        beta=h.pairs(first[6*bs:6*bs+r]);extra=h.unpack({'intervals':points[extra_at:]})
        numeric_forward=[(h.signed256(points[forward_at+10*i:forward_at+10*i+5]),h.signed256(points[forward_at+10*i+5:forward_at+10*i+10])) for i in range(n)]
        y=[(x*s,z*s) for x,z in incoming];expected_balls=[([Z]*n,0) for _ in range(6)];expected_balls[2]=(y,0)
        numeric_error=old_rounds=0
        if old is not None:
            current=list(forwards[old])
            for update in range(old+1,at):
                src=lines[update]['received_from']
                if src is None: continue
                kernel=h.pairing(sources[src],sources[old]);tail_terms+=1
                current=[h.add(x,h.mul(b,kernel)) for x,b in zip(current,betas[update])]
            old_rounds=rounding(current,s2);current_grid=grid(current,s2)
            current_radius=error_bound(et,nt,sources[old],s,old_rounds)
            denominator=s2+sources[old]['norm']
            difference=[h.sub(x,z) for x,z in zip(y,current_grid)]
            expected_beta=[(trunc(x*s2,denominator),trunc(z*s2,denominator)) for x,z in difference]
            if beta!=expected_beta: raise ValueError(f'coercive factor at {at}')
            beta_rounds=sum((v*s2)%denominator!=0 for x in difference for v in x)
            nx=norm(sources[old]['outgoing']+sources[old]['internal'])
            numeric_error=ceildiv(old_rounds,2)+ceildiv(beta_rounds*nx,s)
            et+=numeric_error+ceildiv((nt+norm(y))*sources[old]['radius'],s)
            nt+=ceildiv(norm(beta)*nx,s)
            old_forward,old_error=balls[old]
            expected_balls[1]=(current_grid,current_radius)
            expected_balls[3]=([h.sub(x,z) for x,z in zip(y,old_forward)],old_error)
            expected_balls[4]=([h.sub(x,z) for x,z in zip(current_grid,old_forward)],current_radius+old_error)
            expected_balls[5]=(difference,current_radius)
            epsilon=-1 if old%2 else 1
            for row in range(n):
                signed=h.mul(beta[row],(epsilon,0))
                for col in range(m):
                    M[row][col]=h.add(M[row][col],h.mul(beta[row],h.conj(sources[old]['outgoing'][col])))
                    A[row][col]=h.add(A[row][col],h.mul(signed,h.conj(sources[old]['top'][col])))
                a[row]=h.add(a[row],h.mul(signed,h.conj(sources[old]['bottom'])))
        elif beta!=[Z]*n: raise ValueError('unlinked factor')
        out=apply(M,p);internal=[h.sub(x,z) for x,z in zip(apply(A,P),a)]
        expected=[h.add(x,h.mul(y,(-1 if at%2 else 1,0))) for x,y in zip(out,internal)]
        if expected!=numeric_forward: raise ValueError(f'folded source forward at {at}')
        new_rounds=rounding(expected,s2);new_forward=grid(expected,s2)
        new_error=error_bound(et,nt,source,s,new_rounds);expected_balls[0]=(new_forward,new_error)
        if actual_balls!=expected_balls: raise ValueError(f'oriented current/radius blocks at {at}')
        if extra!=[et,nt,numeric_error,old_rounds,new_rounds]: raise ValueError(f'parameter bounds at {at}')
        sources.append(source);betas.append(beta);forwards.append(expected);balls.append((new_forward,new_error))
        previous=incoming;before=P;ep=jw[4*js-1]
    state=report['body']['material_transport']
    for actual,expected,scale in [(state['outgoing_coefficients'],M,s2),(state['prefix_coefficients'],A,s2)]:
        if [[complex_q(v) for v in row] for row in actual]!=[[(Q(x,scale),Q(y,scale)) for x,y in row] for row in expected]:
            raise ValueError('final folded coefficient state')
    if [complex_q(v) for v in state['birth_offset']]!=[(Q(x,s3),Q(y,s3)) for x,y in a]: raise ValueError('final birth offset')
    if rational(state['coefficient_error'])!=Q(et,s) or rational(state['numerical_coefficient_norm_upper'])!=Q(nt,s): raise ValueError('final parameter bounds')
    if state['birth_occurrences']!=len(lines) or rational(state['numerical_birth_square'])!=Q(geometry.square,s2): raise ValueError('final birth moment')
    if [complex_q(v) for v in state['numerical_birth_cross']]!=[(Q(x,s),Q(y,s)) for x,y in geometry.birth]: raise ValueError('birth cross moment')
    return {'truth_status':'established-bounded','evidence_tags':['computational-witness','measured'],
        'native_current_and_parameter_certificates':len(lines),'older_source_tail_terms':tail_terms,
        'development_symbols':report['development_native_until'],'development_families':len(report['development_records']),
        'native_model_or_learning_executed_by_observer':False,'exact_physical_coefficient_anchor_claim':False,
        'utf8':report.get('utf8'),'disposition':report.get('generation',{}).get('disposition'),'language_quality_established':False}


def main():
    if len(sys.argv)!=4 or sys.argv[2]!='--output': raise SystemExit('usage: inspect_complete_material_transport.py REPORT --output NEW.json')
    result=inspect(json.loads(Path(sys.argv[1]).read_text()))
    with os.fdopen(os.open(sys.argv[3],os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as out:json.dump(result,out,indent=2);out.write('\n')
    print(json.dumps(result))

if __name__=='__main__': main()
