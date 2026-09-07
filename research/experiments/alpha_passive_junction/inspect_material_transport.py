#!/usr/bin/env python3
"""Independent integer certificate for native contextual material transport.

The observer reconstructs numerical factors and every oriented return from immutable reports.
It runs no model update or emission and makes no language-quality claim.
"""
import importlib.util
import json
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('text_current_observer',HERE/'inspect_text_return.py')
if spec is None or spec.loader is None: raise RuntimeError('missing encoder observer')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
D,N=b.D,b.N


def ceildiv(a,d): return -(-a//d)
def trunc(n,d): return -(abs(n)//d) if n<0 else n//d
def product(a,c,scale): return trunc(a*c,scale),int((a*c)%scale!=0)
def complex_product(a,c,scale):
    ac,ra=product(a[0],c[0],scale);bd,rb=product(a[1],c[1],scale)
    ad,rc=product(a[0],c[1],scale);bc,rd=product(a[1],c[0],scale)
    return (ac-bd,ad+bc),ra+rb+rc+rd

def dot(matrix,source,scale):
    out=[];rounds=0
    for row in matrix:
        r=i=0
        for a,c in zip(row,source):
            value,count=complex_product(a,c,scale);r+=value[0];i+=value[1];rounds+=count
        out.extend((r,i))
    return out,rounds

def unpack(section):
    words=section['intervals']
    if section['rows']!=1 or section['width']!=36*N+24 or len(words)!=36*N+24 or any(a!=c for a,c in words):
        raise ValueError('invalid complete transport report')
    values=[]
    for i in range(len(words)//2):
        value=((words[2*i+1][0]&((1<<64)-1))<<64)|(words[2*i][0]&((1<<64)-1))
        values.append(value-(1<<128) if value>=1<<127 else value)
    stride=2*N+1;gain=6*stride;extra=gain+D+1
    return [values[k*stride:(k+1)*stride] for k in range(6)],values[gain:extra],values[extra:]

def norm1(values): return sum(abs(v) for v in values)
def matrix_norm1(matrix): return sum(abs(v) for row in matrix for z in row for v in z)
def prediction_error(error,matrix_l1,source,source_error,rounds,scale):
    return rounds+ceildiv(error*(norm1(source)+source_error),scale)+ceildiv(matrix_l1*source_error,scale)

def bigint(value):
    sign,limbs=value
    return sign*sum(limb<<(32*i) for i,limb in enumerate(limbs))
def rat(value): return Q(bigint(value[0]),bigint(value[1]))


def inspect(report):
    if not report.get('has_material_transport') or not report.get('all_currents_requested'):
        raise ValueError('need the actual learned-transport report and full current history')
    for key in ('native_error','development_error','prompt_error'):
        if report.get(key): raise ValueError(f'refused return: {key}')
    if report['body']['pending_lineage'] is not None or report['body']['pending_symbol'] is not None:
        raise ValueError('uncertain native/application successor')
    history=report['junction_history'];lineages=report['body']['lineage']
    if len(history)!=len(lineages): raise ValueError('incomplete history')
    scale=1<<report['fractional_bits'];sources=3*N
    matrix=[[(0,0)]*sources for _ in range(N)]
    error=0;encoder_h=[0]*D;encoder_prefix=[0]*D;eh=ep=0
    covariance=[[0]*D for _ in range(D)];fields=[];previous=[0]*N
    decoded=[];encoder=[];forwards=[]
    counts={k:0 for k in ('encoder_root_residuals','encoder_bounds','source_dot','three_oriented_differences','gain','coefficient_delta','coefficient_error','forward','forward_error')}
    for at,(lineage,entry) in enumerate(zip(lineages,history)):
        if entry['occurrence']!=at or lineage['occurrence']!=at:
            raise ValueError('chronology mismatch')
        code,incoming=b.input_code(lineage);decoded.append(code)
        raw=[v for a,c in zip(previous,incoming) for v in (a,0,c,0)];fields.append(raw)
        source=lineage['received_from']
        if source is not None:
            if not 0<=source<at: raise ValueError('source is not earlier standing')
            d=fields[source]+[-v for x in incoming for v in (x,0)]
            jd=[v for i in range(0,D,2) for v in (-d[i+1],d[i])]
            for vector in (d,jd):
                support=[(i,x) for i,x in enumerate(vector) if x]
                for i,x in support:
                    for j,y in support: covariance[i][j]+=x*y
        enc=b.unpack(entry['junction']);v,out,h,prefix,u,residual=enc
        expected_u=[x*scale for x in raw]+[0]*(2*N)
        r=[v[i]+sum(covariance[i][j]*v[j] for j in range(D))-2*(u[i]+encoder_h[i]) for i in range(D)]
        if u[:D]!=expected_u or u[D]!=0 or residual[:D]!=r or residual[D]!=1:
            raise ValueError(f'encoder residual/source mismatch at {at}')
        if out[:D]!=[v[i]-u[i] for i in range(D)] or h[:D]!=[2*u[i]+encoder_h[i]-v[i] for i in range(D)] or prefix[:D]!=[encoder_prefix[i]+(-1 if at%2 else 1)*v[i] for i in range(D)]:
            raise ValueError(f'encoder current recurrence mismatch at {at}')
        radius=norm1(r)
        if (v[D],out[D],h[D],prefix[D])!=(2*eh+radius,2*eh+radius,eh+radius,ep+2*eh+radius):
            raise ValueError(f'encoder bound mismatch at {at}')
        counts['encoder_root_residuals']+=1;counts['encoder_bounds']+=1
        encoder_h,encoder_prefix,eh,ep=h[:D],prefix[:D],h[D],prefix[D]
        encoder.append(out)
        blocks,gain,extra=unpack(entry['transport'])
        forward,present,observed,returned,chronology,difference=blocks
        y=[x*scale for a in incoming for x in (a,0)]
        if observed!=y+[0]: raise ValueError(f'observed input mismatch at {at}')
        old_l1=matrix_norm1(matrix)
        if source is not None:
            x=encoder[source][:D];ex=encoder[source][D]
            xp=list(zip(x[::2],x[1::2]))
            prediction,rp=dot(matrix,xp,scale)
            pe=prediction_error(error,old_l1,x,ex,rp,scale)
            if present!=prediction+[pe] or extra[3]!=rp: raise ValueError(f'source prediction mismatch at {at}')
            counts['source_dot']+=1
            old=forwards[source]
            rhat=[a-c for a,c in zip(y,prediction)]
            if returned!=[a-c for a,c in zip(y,old[:2*N])]+[old[2*N]] or chronology!=[a-c for a,c in zip(prediction,old[:2*N])]+[pe+old[2*N]] or difference!=rhat+[pe]:
                raise ValueError(f'oriented return/chronology mismatch at {at}')
            counts['three_oriented_differences']+=1
            denominator=scale+sum(ceildiv(a*a,scale) for a in x)
            dr=sum(int(a*a%scale!=0) for a in x)
            conjugate=[a if i%2==0 else -a for i,a in enumerate(x)]
            expected_gain=[trunc(a*scale,denominator) for a in conjugate]
            ge=ceildiv(dr,2)+sum(int(a*scale%denominator!=0) for a in conjugate)
            if gain!=expected_gain+[ge] or extra[1]!=denominator: raise ValueError(f'gain mismatch at {at}')
            counts['gain']+=1
            g=list(zip(expected_gain[::2],expected_gain[1::2]));rr=list(zip(rhat[::2],rhat[1::2]))
            delta=[];rounds=0
            for row in range(N):
                values=[]
                for column in range(sources):
                    value,rounded=complex_product(rr[row],g[column],scale)
                    values.append(value);rounds+=rounded
                delta.append(values)
            counts['coefficient_delta']+=1
            rounding=ceildiv(rp,2)+ceildiv(norm1(rhat)*ge,scale)+rounds
            error+=ceildiv((old_l1+norm1(y))*ex,scale)+rounding
            if extra[0]!=error or extra[2]!=rounding: raise ValueError(f'coefficient bound mismatch at {at}')
            for i in range(N):
                for j in range(sources):
                    a,c=matrix[i][j],delta[i][j];matrix[i][j]=(a[0]+c[0],a[1]+c[1])
        else:
            if any(any(v for v in block) for block in (present,returned,chronology,difference)) or any(gain) or extra[:4]!=[error,0,0,0]:
                raise ValueError(f'unlinked return manufactures a comparison at {at}')
        counts['coefficient_error']+=1
        prediction,rp=dot(matrix,list(zip(out[:D:2],out[1:D:2])),scale)
        pe=prediction_error(error,matrix_norm1(matrix),out[:D],out[D],rp,scale)
        if forward!=prediction+[pe] or extra[4]!=rp: raise ValueError(f'new forward current/bound mismatch at {at}')
        counts['forward']+=1;counts['forward_error']+=1;forwards.append(forward)
        previous=incoming
    state=report['body']['material_transport']
    for i,row in enumerate(state['coefficients']):
        for j,value in enumerate(row):
            if (rat(value['real']),rat(value['imaginary']))!=(Q(matrix[i][j][0],scale),Q(matrix[i][j][1],scale)):
                raise ValueError('final coefficient matrix differs from native update factors')
    if rat(state['radius'])!=Q(error,scale): raise ValueError('final coefficient error mismatch')
    native_c=report['body']['junction_covariance']['intervals']
    if native_c!=[[x,x] for row in covariance for x in row]+[[1,1]]: raise ValueError('final encoder moment mismatch')
    # Source material is independently compared with the exposure, with no response target used
    # to select developmental inputs.
    records=report['development_records'];frames={}
    with open(report['exposure']) as stream:
        next(stream)
        for line in stream:
            frame=json.loads(line)
            if frame['sequence']>records[-1]['sequence']:break
            frames[frame['sequence']]=frame
    material=parents=0;ends={}
    for record in records:
        frame=frames[record['sequence']]
        if frame['partition']!='development' or frame['family']!=record['family'] or not record['complete']:raise ValueError('source family mismatch')
        visible={p['ordinal']:p for p in frame['views'][0]['visible_parts']}
        for part in record['parts']:
            expected=list(visible[part['ordinal']]['text'].encode())+[256]
            start,end=part['native_from'],part['native_until']
            if decoded[start:end]!=expected:raise ValueError('material/end-of-part mismatch')
            parent=part['parent_source_occurrence']
            if parent is not None:
                family=tuple(record['parent'][k] for k in ('provider','record_group'))
                if ends.get(family)!=parent or any(not view['links'] or any(link['availability']!='prior' or tuple(link['target'][k] for k in ('provider','record_group'))!=family for link in view['links']) for view in frame['views']):raise ValueError('unfounded parent')
                parents+=1
            if lineages[start]['received_from']!=parent:raise ValueError('part source mismatch')
            for index in range(start+1,end):
                if lineages[index]['received_from']!=index-1:raise ValueError('within-part chronology mismatch')
            material+=len(expected)
        ends[tuple(record['family'][k] for k in ('provider','record_group'))]=record['native_until']-1
    if material!=report['development_native_until']:raise ValueError('unaccounted development')
    if decoded[report['prompt_native_from']:report['prompt_native_until']]!=list(report['prompt'].encode())+[256]:raise ValueError('prompt mismatch')
    generation=report['generation'];returned_symbols=0;octets=[]
    for at_reading,reading in enumerate(generation['readings']):
        at=reading['native']['occurrence']
        if at!=generation['native_from']-1+returned_symbols:raise ValueError('generation source skipped or repeated')
        current=forwards[at];masks=[0,0,0,0]
        for bit in range(9):
            gap=current[4*bit+2]-current[4*bit]
            if gap*gap>2*current[2*N]*current[2*N]:masks[0 if gap>0 else 1]|=1<<bit
            else:
                masks[2]|=1<<bit
                if gap==0 and current[2*N]==0:masks[3]|=1<<bit
        if masks!=[reading['native'][k] for k in ('positive','negative','unresolved','exact_zero')]:raise ValueError('material receiver mismatch')
        kind=reading['disposition']['kind']
        if kind=='symbol':
            symbol=reading['disposition']['symbol'];code=256 if symbol['kind']=='end-part' else symbol['value']
            if masks[2] or masks[0]!=code or code>256:raise ValueError('symbol differs from the native current receiver')
            if decoded[at+1]!=code or lineages[at+1]['received_from']!=at:raise ValueError('self-return mismatch')
            returned_symbols+=1
            if code<256:octets.append(code)
        else:
            if at_reading!=len(generation['readings'])-1:raise ValueError('continued past an open codec result')
            if kind=='open' and not masks[2]:raise ValueError('false open result')
            if kind=='reserved' and (masks[2] or masks[0]<=256):raise ValueError('false reserved result')
    if octets!=generation['emitted_octets'] or generation['native_until']-generation['native_from']!=returned_symbols:raise ValueError('emission/accounting mismatch')
    return {'truth_status':'established-bounded','evidence_tags':['computational-witness','measured'],
        'native_occurrences':len(lineages),'development_symbols_checked':material,'shared_parent_contacts_checked':parents,
        'checks':counts,'self_returns_checked':returned_symbols,'emitted_octets':octets,'disposition':generation['disposition'],
        'final_coefficient_radius':str(Q(error,scale)),
        'native_model_or_update_executed_by_observer':False,'language_quality_established':False}


def main():
    if len(sys.argv)!=4 or sys.argv[2]!='--output':raise SystemExit('usage: inspect_material_transport.py REPORT --output NEW.json')
    result=inspect(json.loads(Path(sys.argv[1]).read_text()))
    with os.fdopen(os.open(sys.argv[3],os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as out:json.dump(result,out,indent=2);out.write('\n')
    print(json.dumps(result))


if __name__=='__main__':main()
