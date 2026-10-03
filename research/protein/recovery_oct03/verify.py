#!/usr/bin/env python3
"""Portable exact source and receiving replay; no search or native generator.

SPDX-License-Identifier: MIT OR Apache-2.0
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys, time

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
sys.dont_write_bytecode = True
sys.path.insert(0,str(BASE))
import exact as m
spec = importlib.util.spec_from_file_location('protein_pinned_reader',BASE/'verify.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
need = m.need
PIN = 'f6a8455b5efb0e4947719c2ebfa9c3d715dfb3cc'
P = 2**96
CHARTS = ['R','F']
ORIGINAL = [(-F(1,16),F(0)),(F(0),F(1,16))]
EIGHTH = [(-F(1,16),-F(3,64)),(F(1,32),F(1,16))]
UPPER = [(-F(1,16),-F(3,64)),(F(3,64),F(1,16))]

def load(name):return json.loads((ROOT/name).read_text())
def decode(t):return {tuple(map(int,k.split(','))) if k else ():tuple(map(F,v)) for k,v in t.items()}
def encode(t):return {','.join(map(str,k)):[str(v[0]),str(v[1])] for k,v in t.items()}
def primary(t):return {tuple(r['powers']):tuple(F(int(x),P) for x in r['outward_coefficients']) for r in t}
def overlap(a,b):return max(a[0],b[0])<=min(a[1],b[1])
def coefficient_agreement(a,b):
    need(set(a)==set(b),'same source coefficient identities')
    need(all(overlap(a[k],b[k]) for k in a),'exact outward source coefficients agree')
    return len(a)
def region(t,active,box):return base.bernstein(t,active,CHARTS,box)
def bounds(path):
    box=list(ORIGINAL)
    for bit in path:
        need(bit in '01','binary restriction')
        k=0 if box[0][1]-box[0][0]>=box[1][1]-box[1][0] else 1
        mid=sum(box[k])/2
        box[k]=(box[k][0],mid) if bit=='0' else (mid,box[k][1])
    return box
def declared_box(row):return [tuple(map(F,b)) for b in row['bounds']]
def kraft(rows):
    paths=[r['relative_path'] for r in rows];unique=set(paths)
    need(len(unique)==len(paths) and all(p[:n] not in unique for p in paths for n in range(len(p))),'prefix-free restriction cover')
    need(sum((F(1,2**len(p)) for p in paths),F(0))==1,'complete Kraft sum')
    for r in rows:need(bounds(r['relative_path'])==declared_box(r),'exact restriction address and bounds')

def integer_region(t,active,box):
    # Exact denominator-cleared Bernstein is the original 96-grain receiver.
    packed=[(0,0)]*9
    for r in t:
        ij=[0,0]
        for n,k in zip(r['powers'],active):ij[k]=2-n if CHARTS[k]=='R' else n
        packed[3*ij[0]+ij[1]]=tuple(map(int,r['outward_coefficients']))
    def weights(interval):
        lo,hi=interval;g=lcm(lo.denominator,hi.denominator);a=int(lo*g);z=int(hi*g);w=z-a
        return ((2*g*g,2*a*g,2*a*a),(2*g*g,(2*a+w)*g,2*a*z),(2*g*g,2*z*g,2*z*z)),2*g*g
    def weighted(values,ws):
        lo=hi=0
        for (a,b),w in zip(values,ws):
            lo+=(a if w>=0 else b)*w;hi+=(b if w>=0 else a)*w
        return lo,hi
    w0,d0=weights(box[0]);w1,d1=weights(box[1])
    first=[[weighted([packed[k*3+j] for k in range(3)],ws) for j in range(3)] for ws in w0]
    b=[weighted(first[i],ws) for i in range(3) for ws in w1]
    return F(min(v[0] for v in b),P*d0*d1),F(max(v[1] for v in b),P*d0*d1)

def pins():
    manifest=load('manifest.json');need(manifest['base_commit']==PIN,'published dependency commit pin')
    for root,entries in [(ROOT,manifest['files']),(BASE,manifest['base_dependencies'])]:
        for name,entry in entries.items():
            b=(root/name).read_bytes()
            need(hashlib.sha256(b).hexdigest()==entry['sha256'] and len(b)==entry['bytes'],'portable input identity '+name)
    need(len(manifest['files'])==7 and manifest['selected_nested_machine_paths_sanitized']==1088,'manifest scope')
    for name in manifest['files']:
        text=(ROOT/name).read_text()
        forbidden=[chr(47)+'home'+chr(47),chr(47)+'tmp'+chr(47),'Sent'+'inel_']
        need(not any(x in text for x in forbidden),'no machine path or private authorization text')
    return manifest

def family():
    d=json.loads((BASE/'data/source_faces.json').read_text());g=int(d['grain_denominator'])
    need(g==2**32 and len(d['source_faces'])==len(d['atoms'])==1108 and len(d['edges'])==1107,'complete pinned source')
    ns={i:set() for i in range(1108)}
    for a,b in d['edges']:ns[a].add(b);ns[b].add(a)
    points={}
    for i,r in enumerate(d['source_faces']):
        need(r['atom_id']==i,'canonical source index')
        points[i]=[m.rebase((F(a,g),F(b,g))) for a,b in r['box']]
        for guards in r['denominator_guards']:
            for lo,hi in guards:
                lo,hi=F(lo),F(hi);need(lo<=hi and (lo>0 or hi<0),'selected source branch guard')
        if d['atoms'][i]['element']=='H':need(r['root_context_id'] in d['local_context_bindings'],'H local root chart identity')
    r=d['selected_OXT_root'];lo,hi=map(F,r['enclosure']);s=F(r['square'])
    need(r['selected_embedding']=='positive' and 0<lo<=hi and lo*lo<=s<=hi*hi,'retained OXT root branch')
    f=base.Family(points,ns,d['joint_axes'],(434,433,F(-19,64)))
    return d,ns,f

def progress(kind,index,tick,args,start):
    elapsed=time.monotonic_ns()-tick
    if args.unit_upper_ns:
        need(elapsed<=args.unit_upper_ns,'fixed per-unit projection exceeded; stop without raised limit')
    print(json.dumps({'unit':kind,'index':index,'unit_ns':elapsed,'elapsed_ns':time.monotonic_ns()-start}),flush=True)
    return elapsed

def verify_source(args,start):
    c=load('conditions.json');r=load('receivers.json');d,ns,f=family()
    need(c['fixed_controls']=={'phi26':'-19/64','beta':'0'} and c['axes_fixed_moved']==d['joint_axes'],'same fixed source word')
    need([set(x) for x in c['complete_support_ids']]==f.supports,'actual complete cuts')
    defs=c['selected_necessary_comparisons'];conditions=c['source_conditions']
    need(len(defs)==1342 and sum(x['kind']=='internal' for x in defs)==1202 and len(conditions)==1206,'complete retained comparison population')
    old=json.loads((BASE/'data/comparisons.json').read_text())['comparisons']
    for row in old:
        x=defs[row['index']]
        need(x['pair']==row['pair'] and x['kind']==row['kind'] and F(x['severe_q_threshold_A2'])==F(row['threshold_A2']),'old comparison operands retained')
    new={x['comparison']:x for x in r['rows']}
    need(sorted(new)==list(range(376,1342)),'all 966 new identities')
    need(len({tuple(x['pair']) for x in new.values()})==966,'new pair uniqueness')
    counts=Counter();checks=0;units=[]
    limits={'necessary':list(map(F,d['necessary_chord_q_outer_A2'])),'sufficient':list(map(F,d['sufficient_chord_q_inner_A2']))}
    ports={f.relative(*row['pair'])[::2] for row in conditions}
    need(len(ports)<=512,'resident source moment partition fits pinned owner cache')
    for a,active in ports:f.moments(a,active)
    for index,row in enumerate(conditions):
        tick=time.monotonic_ns();a,b=row['pair'];active,N,D=f.face(a,b)
        need(list(active)==row['active_controls'],'actual active control word')
        need(list(f.relative(a,b)[:2])==row['relative_pair'],'actual common-motion cancellation')
        threshold=F(row['threshold_A2']);upper=isinstance(row['comparison'],str) and row['comparison'].endswith('_upper')
        if isinstance(row['comparison'],int):
            definition=defs[row['comparison']]
            need(definition['kind']=='internal' and definition['pair']==row['pair'] and threshold==F(definition['severe_q_threshold_A2']),'condition joined to actual comparison')
            excluded=ns[a]|{z for y in ns[a] for z in ns[y]}
            need(a!=b and b not in excluded,'actual nonlocal pair')
            radii=d['radii_A'];need(threshold==F(4,9)*(F(radii[d['atoms'][a]['element']])+F(radii[d['atoms'][b]['element']]))**2,'declared exact aperture')
            polar={'N','O','S'}
            donor=lambda x:d['atoms'][x]['element']=='H' and any(d['atoms'][y]['element'] in polar for y in ns[x])
            need(not ((d['atoms'][a]['element'] in polar and d['atoms'][b]['element'] in polar) or (donor(a) and d['atoms'][b]['element'] in polar) or (donor(b) and d['atoms'][a]['element'] in polar)),'all nondirectional conditions remain separate')
            counts[','.join(map(str,active))]+=1
        else:
            role=row['chord_bound_role'];need(row['pair']==[64,818] and threshold==limits[role][int(upper)],'necessary/sufficient chord bound law')
        G={p:m.sub(N[p],m.scale(D[p],threshold)) for p in N}
        if upper:G={p:m.scale(v,-1) for p,v in G.items()}
        checks+=coefficient_agreement(primary(row['numerator']),N)+coefficient_agreement(primary(row['denominator']),D)+coefficient_agreement(primary(row['slack']),G)
        if row['comparison'] in new:
            x=new[row['comparison']]
            for name in ['pair','relative_pair','active_controls','threshold_A2','numerator','denominator','slack']:need(row[name]==x[name],'literal cumulative consumer join')
            need(encode(N)==x['independent_numerator'] and encode(D)==x['independent_denominator'] and encode(G)==x['independent_slack'],'all independent source tensors rebuilt exactly')
        need(region(G,active,EIGHTH)[0]>0,'fresh independent source condition clears accepted eighth')
        need(integer_region(row['slack'],active,EIGHTH)[0]>0,'primary condition clears accepted eighth')
        units.append(progress('source-condition',index,tick,args,start))
    need(dict(counts)==c['active_word_counts']=={'0,1':1201,'0':1},'corrected internal active-word counts')
    return {'passed':True,'part':'source','source_conditions_rebuilt':1206,'internal_comparisons':1202,'chord_faces':4,'new_receivers_rebuilt':966,'independent_coefficient_checks':checks,'accepted_eighth_verified':True,'upperchild_inherits_all1202_and_chords':all(EIGHTH[k][0]<=UPPER[k][0]<=UPPER[k][1]<=EIGHTH[k][1] for k in range(2)),'max_unit_ns':max(units)}

def verify_regions(args,start):
    r=load('receivers.json');c=load('conditions.json');cover=load('region_cover.json')
    rows={x['comparison']:x for x in r['rows']};ind={k:decode(x['independent_slack']) for k,x in rows.items()};root_counts=Counter();checks=0
    for row in r['rows']:
        tick=time.monotonic_ns();k=row['comparison'];h=integer_region(row['slack'],row['active_controls'],ORIGINAL);ih=region(ind[k],row['active_controls'],ORIGINAL)
        need(list(map(str,h))==row['primary_whole_region_G'] and list(map(str,ih))==row['independent_whole_region_G'],'original region readings reproduced exactly')
        status='admitted' if h[0]>0 and ih[0]>0 else 'refused' if h[1]<0 and ih[1]<0 else 'unresolved';root_counts[status]+=1
        progress('root-receiver',k,tick,args,start)
    root_partition={k:root_counts[k] for k in ['admitted','refused','unresolved']}
    need(root_partition==r['root_counts']=={'admitted':644,'refused':0,'unresolved':322},'root exact receiving partition')
    def reading(k,box):
        x=rows[k];return integer_region(x['slack'],x['active_controls'],box),region(ind[k],x['active_controls'],box)
    def certificate(record):
        nonlocal checks
        box=declared_box(record);need(bounds(record['relative_path'])==box,'cell restriction')
        for v in record['new_strictly_admitted_comparisons']:
            h,ih=reading(v['comparison'],box);need(h[0]>0 and ih[0]>0,'two positive regional lower bounds')
            need(str(h[0])==v['primary_lower_G'] and str(ih[0])==v['independent_lower_G'],'recorded positive signs retained exactly');checks+=2
        witness=record['witness']
        if witness:
            k=witness['comparison'];x=rows[k];h,ih=reading(k,box);need(h[1]<0 and ih[1]<0,'two negative regional upper bounds')
            dh=integer_region(x['denominator'],x['active_controls'],box);idh=region(decode(x['independent_denominator']),x['active_controls'],box)
            need(dh[0]>0 and idh[0]>0,'positive denominator at obstruction')
            upper=max(F(x['threshold_A2'])+h[1]/dh[1],F(x['threshold_A2'])+ih[1]/idh[1])
            need(upper==F(witness['quadrance_upper_A2'])<F(witness['threshold_A2']),'strict exact quadrance obstruction');checks+=4
    for record in cover['quarters']+cover['refinement_records']:certificate(record)
    kraft(cover['nondirectional_original_region_leaves']);kraft(cover['complete_combined_geometric_cover'])
    need(cover['nondirectional_Kraft_sum']==cover['combined_Kraft_sum']=='1','reported coverage')
    direction=load('directional_geometry.json');pair=cover['pair64_830_refinement'];x=next(r for r in direction['quadrance_rows'] if r['pair']==[64,830]);iG=decode(x['independent_diagnostic_slack'])
    for rec in [pair['exact_control_point_reading']]+pair['complete_region_cover']:
        box=[tuple(map(F,b)) for b in rec['control_bounds']];h=integer_region(x['diagnostic_slack'],x['active_controls'],box);ih=region(iG,x['active_controls'],box)
        need(list(map(str,h))==rec['primary_G'] and list(map(str,ih))==rec['independent_G'],'exact pair refinement readings')
        dh=integer_region(x['denominator'],x['active_controls'],box);idh=region(decode(x['independent_denominator']),x['active_controls'],box)
        need(dh[0]>0 and idh[0]>0,'pair-refinement denominator positive')
        status='admitted' if h[0]>0 and ih[0]>0 else 'refused' if h[1]<0 and ih[1]<0 else 'unresolved'
        need(status==rec['status'],'pair-refinement exact sign status')
        if rec['witness']:
            upper=max(F(x['diagnostic_threshold_A2'])+h[1]/dh[1],F(x['diagnostic_threshold_A2'])+ih[1]/idh[1])
            need(upper==F(rec['witness']['quadrance_upper_A2'])<2<F(x['diagnostic_threshold_A2']),'exact control-point fixture obstruction')
    for record,cached in zip(c['source_conditions'],c['cached_RF_G_receivers']):
        packed=[(0,0)]*9
        for coefficient in record['slack']:
            ij=[0,0]
            for n,k in zip(coefficient['powers'],record['active_controls']):ij[k]=2-n if CHARTS[k]=='R' else n
            packed[ij[0]*3+ij[1]]=tuple(map(int,coefficient['outward_coefficients']))
        need([[str(x) for x in v] for v in packed]==cached['G_coefficients'],'cached RF consumer is literal chart reversal')
    return {'passed':True,'part':'regions','new_root_receivers':966,'root_counts':root_partition,'regional_sign_checks':checks,'original_region_Kraft':'1','combined_region_Kraft':'1','pair64_830_corner_obstruction_reproduced':True,'upperchild_additional_aperture_clear':True,'lowerchild_unresolved':True,'entire_eighth_exclusion_claim':False}

def verify_directional(args,start):
    data=load('directional_geometry.json');d,ns,f=family();common=decode(data['independent_common_denominator']);primary_common=primary(data['common_denominator']);checks=coefficient_agreement(primary_common,common);by_pair={};qranges={};counts=Counter();units=[]
    rebuilt_common={}
    for powers in product(range(3),repeat=2):
        v=m.val(1)
        for degree,k in zip(powers,range(2)):v=m.mul(v,[m.val(1),m.val(0),f.qs[k]][degree])
        rebuilt_common[powers]=v
    need(rebuilt_common==common,'common denominator rebuilt from actual source axes')
    def lift(t,active):
        out={}
        for powers in product(range(3),repeat=2):
            v=t[tuple(powers[k] for k in active)]
            for k in range(2):
                if k not in active:v=m.mul(v,[m.val(1),m.val(0),f.qs[k]][powers[k]])
            out[powers]=v
        return out
    ports={f.relative(*row['pair'])[::2] for row in data['quadrance_rows']}
    need(len(ports)<=512,'resident directional source moment partition')
    for a,active in ports:f.moments(a,active)
    for row in data['quadrance_rows']:
        tick=time.monotonic_ns();active,N,D=f.face(*row['pair'])
        need(list(active)==row['active_controls'],'directional active source word')
        need(encode(N)==row['independent_numerator'] and encode(D)==row['independent_denominator'],'all source directional quadrances rebuilt')
        checks+=coefficient_agreement(primary(row['numerator']),N)+coefficient_agreement(primary(row['denominator']),D)
        full=lift(N,active);need(encode(full)==row['independent_full_common_denominator_numerator'],'only absent denominator factors are lifted');checks+=coefficient_agreement(primary(row['full_common_denominator_numerator']),full)
        by_pair[tuple(row['pair'])]=full
        nh,dh=region(N,active,EIGHTH),region(D,active,EIGHTH);q=[a/b for a in nh for b in dh];need(dh[0]>0,'positive quadrance denominator')
        iq=[max(F(0),min(q)),max(q)];need(list(map(str,iq))==row['independent_quadrance_A2'],'exact independent quadrance enclosure')
        pn=integer_region(row['numerator'],active,EIGHTH);pd=integer_region(row['denominator'],active,EIGHTH)
        need(pd[0]>0,'primary quadrance denominator positive')
        pq=[a/b for a in pn for b in pd];pq=[max(F(0),min(pq)),max(pq)]
        need(list(map(str,pq))==row['quadrance_A2'],'primary quadrance enclosure reproduced exactly')
        qranges[tuple(row['pair'])]=(pq,iq)
        if 'diagnostic_threshold_A2' in row:
            G={p:m.sub(N[p],m.scale(D[p],F(row['diagnostic_threshold_A2']))) for p in N};need(encode(G)==row['independent_diagnostic_slack'],'declared diagnostic aperture source equation')
            h,ih=integer_region(row['diagnostic_slack'],active,EIGHTH),region(G,active,EIGHTH)
            status='above_diagnostic_aperture' if h[0]>0 and ih[0]>0 else 'below_diagnostic_aperture' if h[1]<0 and ih[1]<0 else 'unresolved_diagnostic_aperture';need(status==row['diagnostic_status'],'directional diagnostic sign');counts[status]+=1
        units.append(progress('directional-quadrance',row['request_index'],tick,args,start))
    angle_counts=Counter();dr=region(common,(0,1),EIGHTH);pdr=integer_region(data['common_denominator'],(0,1),EIGHTH)
    need(dr[0]>0 and pdr[0]>0,'positive common denominator')
    need(list(map(str,dr))==data['independent_common_denominator_region'] and list(map(str,pdr))==data['primary_common_denominator_region'],'both denominator readings reproduced')
    for row in data['orientation_rows']:
        tick=time.monotonic_ns();get=lambda a,b:by_pair[tuple(sorted((a,b)))]
        a,b,c=get(row['D'],row['H']),get(row['H'],row['A']),get(row['D'],row['A']);K={p:m.sub(m.add(a[p],b[p]),c[p]) for p in common}
        need(encode(K)==row['independent_dot_numerator_K'],'D-H-A source common-denominator equation');checks+=coefficient_agreement(primary(row['dot_numerator_K']),K)
        h,ih=integer_region(row['dot_numerator_K'],(0,1),EIGHTH),region(K,(0,1),EIGHTH)
        status='greater_than_quarter_turn' if h[1]<0 and ih[1]<0 else 'less_than_quarter_turn' if h[0]>0 and ih[0]>0 else 'exact_quarter_turn' if h==ih==(F(0),F(0)) else 'unresolved_quarter_turn_sign'
        need(status==row['angle_at_H_partition'],'angle sign partition');angle_counts[status]+=1
        vals=[a/b for a in ih for b in tuple(2*x for x in dr)];iL=[min(vals),max(vals)]
        need(list(map(str,iL))==row['independent_dot_A2'],'independent physical dot units')
        vals=[a/b for a in h for b in tuple(2*x for x in pdr)];pL=[min(vals),max(vals)]
        need(list(map(str,pL))==row['dot_A2'],'primary physical dot units')
        dhq,haq=qranges[tuple(sorted((row['D'],row['H'])))],qranges[tuple(sorted((row['H'],row['A'])))]
        if all(x[0]>0 for pair in [dhq,haq] for x in pair):
            for owner,L in enumerate([pL,iL]):
                lo=F(0) if L[0]<=0<=L[1] else min(x*x for x in L);hi=max(x*x for x in L)
                product_q=[dhq[owner][0]*haq[owner][0],dhq[owner][1]*haq[owner][1]]
                values=[x/y for x in [lo,hi] for y in product_q];cs=[max(F(0),min(values)),min(F(1),max(values))]
                name='cosine_squared' if owner==0 else 'independent_cosine_squared'
                need(list(map(str,cs))==row[name],'signed angle normalization and Cauchy enclosure reproduced')
        else:
            need(row['normalization']=='unresolved zero-separation fibre; no angle normalized','zero-separation fibre remains open')
        units.append(progress('directional-angle',row['orientation_index'],tick,args,start))
    need(len(data['directional_obligations'])==110 and len(data['orientation_rows'])==76 and len(data['no_DHA_obligations'])==12,'all separate obligations retained')
    used={i for t in data['source_orientation_triples'] for i in t['source_obligation_indices']}
    need({r['obligation_index'] for r in data['no_DHA_obligations']}==set(range(110))-used,'exact no-DHA retained complement')
    need(dict(counts)==data['diagnostic_aperture_counts'] and dict(angle_counts)==data['angle_partition_counts'],'all directional partitions reproduced')
    return {'passed':True,'part':'directional','quadrances_rebuilt':161,'DHA_faces_rebuilt':76,'diagnostic_counts':dict(counts),'angle_counts':dict(angle_counts),'no_DHA_obligations_retained':12,'all110_flags_retained':True,'independent_coefficient_checks':checks,'max_unit_ns':max(units),'chemical_or_material_admission':False}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=['source','regions','directional'],required=True)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--unit-upper-ns',type=int,default=0)
    args=parser.parse_args();start=time.monotonic_ns();pins()
    result={'source':verify_source,'regions':verify_regions,'directional':verify_directional}[args.part](args,start)
    result.update(wall_ns=time.monotonic_ns()-start,base_commit=PIN,source_uncertainty_quantified=False,target_pose_constructed=False,fold_binding_or_pH_claimed=False)
    if args.output:
        with args.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__':main()
