#!/usr/bin/env python3
"""Exact cold geometry of the complete internal-current source; no model update or emitter.

Native report centres are numerical representatives. Their existing radii remain explicit.
Integer pairings here verify a factorization of those representatives, not a point seal.
"""
import json
import math
import os
import sys
from pathlib import Path

ZERO = (0, 0)
def add(a, b): return a[0]+b[0], a[1]+b[1]
def sub(a, b): return a[0]-b[0], a[1]-b[1]
def neg(a): return -a[0], -a[1]
def conj(a): return a[0], -a[1]
def mul(a, b): return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]
def dot(a, b):
    out = ZERO
    for x, y in zip(a, b): out = add(out, mul(conj(x), y))
    return out
def pairs(values): return list(zip(values[::2], values[1::2]))
def bits(a): return max(abs(a[0]).bit_length(), abs(a[1]).bit_length())


class PrefixGeometry:
    def __init__(self, width):
        self.width = width
        self.covariance = [[ZERO for _ in range(width)] for _ in range(width)]
        self.birth = [ZERO]*width
        self.square = 0
        self.contacts = []
        self.trace = 0

    def admit(self, at, contact, before, before_error=0):
        c = dot(contact, before)
        for i, d in enumerate(contact):
            self.birth[i] = add(self.birth[i], mul(d, c))
            for j, e in enumerate(contact):
                self.covariance[i][j] = add(self.covariance[i][j], mul(d, conj(e)))
        self.square += dot([c], [c])[0]
        self.trace += dot(contact, contact)[0]
        self.contacts.append((at, contact, c, before_error))

    def source(self, at, outgoing, prefix, out_error=0, prefix_error=0):
        top = []
        for row, birth in zip(self.covariance, self.birth):
            value = ZERO
            for c, p in zip(row, prefix): value = add(value, mul(c, p))
            top.append(sub(value, birth))
        bottom = sub(dot(self.birth, prefix), (self.square, 0))
        epsilon = -1 if at % 2 else 1
        internal = [mul((epsilon, 0), sub(dot(d, prefix), c)) for _, d, c, _ in self.contacts]
        full = list(outgoing)+internal
        norm = dot(full, full)
        factored = add(dot(outgoing, outgoing), sub(dot(top, prefix), conj(bottom)))
        if norm != factored or norm[1] != 0 or norm[0] < 0:
            raise ValueError('full-source norm does not agree with the prefix moment')
        trace_root = math.isqrt(self.trace)
        trace_root += trace_root*trace_root != self.trace
        error = out_error + 2*prefix_error*trace_root
        individual_square = sum(dot(d, d)[0]*(prefix_error+birth_error)**2
                                for _, d, _, birth_error in self.contacts)
        if any(birth_error > prefix_error for _, _, _, birth_error in self.contacts):
            raise ValueError('prefix error chronology is not monotone')
        if (error-out_error)**2 < individual_square:
            raise ValueError('full internal-current error bound is insufficient')
        return {'at':at, 'outgoing':list(outgoing), 'prefix':list(prefix), 'top':top,
                'bottom':bottom, 'internal':internal, 'norm':norm[0], 'radius':error,
                'contacts':len(internal), 'trace':self.trace}


def pairing(a, b):
    if a['at'] > b['at']: return conj(pairing(b, a))
    historical = sub(dot(a['top'], b['prefix']), conj(a['bottom']))
    if (a['at']+b['at']) % 2: historical = neg(historical)
    return add(dot(a['outgoing'], b['outgoing']), historical)


def direct_pairing(a, b):
    # zip is the actual common born-contact population; unborn coordinates extend by zero.
    return add(dot(a['outgoing'], b['outgoing']), dot(a['internal'], b['internal']))


def compare_receivers(sources, returns):
    """Algebraic covectors, not fitted answers: compare complete rows, folded current and caches."""
    width = len(sources[0]['prefix'])
    direct_coefficients = []
    out = [ZERO]*width
    top = [ZERO]*width
    bottom = ZERO
    cached = [ZERO]*len(sources)
    checks = 0
    for source_at, beta in returns:
        source = sources[source_at]
        direct_coefficients.append((source, beta))
        epsilon = (-1 if source['at'] % 2 else 1, 0)
        for i in range(width):
            out[i] = add(out[i], mul(beta, conj(source['outgoing'][i])))
            top[i] = add(top[i], mul(mul(beta, epsilon), conj(source['top'][i])))
        bottom = add(bottom, mul(mul(beta, epsilon), conj(source['bottom'])))
        for j, target in enumerate(sources):
            cached[j] = add(cached[j], mul(beta, pairing(source, target)))
            direct = ZERO
            for old, coefficient in direct_coefficients:
                direct = add(direct, mul(coefficient, direct_pairing(old, target)))
            if cached[j] != direct: raise ValueError('live receiver current differs')
            checks += 1
            if target['at'] >= max(old['at'] for old, _ in direct_coefficients):
                fixed = sum_complex(mul(a,b) for a,b in zip(out,target['outgoing']))
                h = sub(sum_complex(mul(a,b) for a,b in zip(top,target['prefix'])), bottom)
                if target['at'] % 2: h = neg(h)
                if add(fixed,h) != direct: raise ValueError('future folded current differs')
                checks += 1
    return checks


def sum_complex(values):
    result = ZERO
    for value in values: result = add(result,value)
    return result


def complex_controls():
    geometry = PrefixGeometry(2)
    before = [ZERO,ZERO]
    sources = []
    for at in range(5):
        d = [(at+1,(-1)**at), (1-at,2)]
        geometry.admit(at,d,before)
        prefix = [(2-at,at+1),(at*at-1,3-at)]
        sources.append(geometry.source(at,[(at+1,2),(1,at)],prefix))
        before = prefix
    for a in sources:
        for b in sources:
            if pairing(a,b) != direct_pairing(a,b): raise ValueError('complex source pairing differs')
    if not any(pairing(a,b)[1] for a in sources for b in sources): raise ValueError('phase control is vacuous')
    return {'pairings':25, 'receiver_equalities':compare_receivers(sources,[(0,(1,2)),(3,(-2,1)),(1,(3,-1)),(3,(-1,-2))])}


def unpack(section):
    points=section['intervals']
    if any(a!=b for a,b in points) or len(points)%2: raise ValueError('packed point wire')
    values=[]
    for at in range(0,len(points),2):
        value=(points[at][0] & ((1<<64)-1)) | ((points[at+1][0] & ((1<<64)-1))<<64)
        values.append(value-(1<<128) if value & (1<<127) else value)
    return values


def signed256(points):
    if len(points)!=5 or any(a!=b for a,b in points) or points[4][0] not in (0,1):
        raise ValueError('signed-magnitude source wire')
    value=sum((point[0]&((1<<64)-1))<<(64*i) for i,point in enumerate(points[:4]))
    return -value if points[4][0] else value


def check_native_source(captured, source, width, grain):
    points=captured['source']['intervals'];d=2*width
    if len(points)!=6*d+22 or any(a!=b for a,b in points): raise ValueError('native full-source extent')
    values=unpack({'intervals':points[:6*d]})
    if pairs(values[:d])!=source['outgoing'] or pairs(values[d:2*d])!=source['prefix'] or pairs(values[2*d:])!=source['top']:
        raise ValueError('native source vectors differ from complete history')
    bottom=(signed256(points[6*d:6*d+5]),signed256(points[6*d+5:6*d+10]))
    norm=signed256(points[6*d+10:6*d+15]);radius=unpack({'intervals':points[6*d+16:6*d+18]})[0]
    norm_upper=unpack({'intervals':points[6*d+20:6*d+22]})[0]
    if (bottom!=source['bottom'] or norm!=source['norm'] or radius!=source['radius']
            or points[6*d+15][0]!=grain or points[6*d+18][0]!=source['trace']
            or points[6*d+19][0]!=source['at'] or captured['occurrence']!=source['at']):
        raise ValueError('native source scalar/chronology differs')
    if norm_upper<0 or norm_upper*norm_upper<norm or (norm_upper and (norm_upper-1)**2>=norm):
        raise ValueError('native representative norm is not the exact upward square root')


def inspect(report, native=None):
    controls=complex_controls()
    lines=report['body']['lineage']; history=report['junction_history']
    if not lines or len(history)!=len(lines): raise ValueError('complete native history is required')
    nodes=len(lines[0]['incoming']); width=3*nodes; stride=2*width+1
    geometry=PrefixGeometry(width); previous=[ZERO]*nodes; raw=[]; sources=[]
    before=[ZERO]*width; before_error=0; extent={ 'birth':0, 'square':0, 'top':0, 'bottom':0, 'norm':0 }
    selected={r['native_until']-1 for r in report['development_records']}
    selected.update([0,1,2,len(lines)-1])
    checked_native=0
    if native is not None:
        if native['construction_error'] or native['boundary_error'] or native['native_occurrences']!=len(native['source_geometry']):
            raise ValueError('native source construction did not return')
        if native['lineage']!=lines[:native['native_occurrences']]: raise ValueError('native construction field differs from reference')
    for at,(line,captured) in enumerate(zip(lines,history)):
        if (line['occurrence']!=at or captured['occurrence']!=at or line['frame']!=0
                or line['predecessor_state']!=(at-1 if at else None)):
            raise ValueError('observer requires its declared root frame and chronology')
        if len(line['incoming'])!=nodes: raise ValueError('incoming source extent')
        if any(v['denominator']!=1 for v in line['incoming']): raise ValueError('observer integral contact chart')
        incoming=[(v['real'],v['imaginary']) for v in line['incoming']]
        raw.append([value for a,b in zip(previous,incoming) for value in (a,b)])
        if line['received_from'] is not None:
            if not 0<=line['received_from']<at: raise ValueError('source has not occurred')
            d=raw[line['received_from']]+[neg(v) for v in incoming]
            geometry.admit(at,d,before,before_error)
        words=unpack(captured['junction'])
        if len(words)!=6*stride: raise ValueError('enclosed report extent')
        outgoing=pairs(words[stride:stride+2*width]); prefix=pairs(words[3*stride:3*stride+2*width])
        source=geometry.source(at,outgoing,prefix,words[2*stride-1],words[4*stride-1])
        if native is not None and at<len(native['source_geometry']):
            check_native_source(native['source_geometry'][at],source,width,report['fractional_bits'])
            checked_native+=1
            if checked_native==len(native['source_geometry']):
                state=native['history_geometry_state']['intervals'];d=2*width
                if pairs(unpack({'intervals':state[:2*d]}))!=geometry.birth or signed256(state[2*d:2*d+5])!=geometry.square:
                    raise ValueError('native final birth moment differs')
                if [p[0] for p in state[2*d+5:]]!=[at+1,report['fractional_bits'],0]: raise ValueError('native moment chronology differs')
                real=[]
                for row in geometry.covariance:
                    real.append([v for a,b in row for v in (a,-b)])
                    real.append([v for a,b in row for v in (b,a)])
                if native['covariance']['intervals']!=[[v,v] for row in real for v in row]+[[1,1]]:
                    raise ValueError('native moment and field covariance disagree')
        if at in selected: sources.append(source)
        extent['birth']=max(extent['birth'],*(bits(v) for v in geometry.birth))
        extent['square']=max(extent['square'],geometry.square.bit_length())
        extent['top']=max(extent['top'],*(bits(v) for v in source['top']))
        extent['bottom']=max(extent['bottom'],bits(source['bottom']))
        extent['norm']=max(extent['norm'],source['norm'].bit_length())
        before,before_error=prefix,words[4*stride-1]; previous=incoming
    checked=0
    for a in sources:
        for b in sources:
            if pairing(a,b)!=direct_pairing(a,b): raise ValueError('actual full-history pairing differs')
            checked+=1
    receivers=compare_receivers(sources,[(0,(1,2)),(len(sources)-1,(-2,1)),(1,(3,-1)),(len(sources)//2,(1,1))])
    return {'truth_status':'established-bounded','evidence_tags':['computational-witness'],
        'scope':'exact algebra on native numerical representatives, with full-source error bounds',
        'native_occurrences':len(lines),'native_source_certificates':checked_native,'source_cuts':[s['at'] for s in sources],
        'pairing_equalities':checked,'receiver_equalities':receivers,'complex_controls':controls,
        'maximum_numerator_bits':extent,'fractional_bits':report['fractional_bits'],
        'native_model_or_learning_executed':False,'language_quality_established':False}


def main():
    if len(sys.argv) not in (4,6) or sys.argv[2]!='--output' or (len(sys.argv)==6 and sys.argv[4]!='--native-source'):
        raise SystemExit('usage: current_history_source.py REPORT --output NEW.json [--native-source NATIVE.json]')
    native=json.loads(Path(sys.argv[5]).read_text()) if len(sys.argv)==6 else None
    result=inspect(json.loads(Path(sys.argv[1]).read_text()),native)
    with os.fdopen(os.open(sys.argv[3],os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as out:
        json.dump(result,out,indent=2);out.write('\n')
    print(json.dumps(result))

if __name__=='__main__': main()
