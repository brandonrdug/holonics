#!/usr/bin/env python3
"""Source, final moment and emitted-current inspection for a broader native text exposure.

This does not claim a full historical coefficient certificate when that history was not read out.
"""
import importlib.util
import json
import os
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('material_transport_inspection',HERE/'inspect_material_transport.py')
if spec is None or spec.loader is None:raise RuntimeError('missing current inspector')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
b=m.b;D,N=b.D,b.N


def inspect(r):
    if not r.get('has_material_transport') or any(r.get(k) for k in ('native_error','development_error','prompt_error')):raise ValueError('native/material exposure did not return')
    if r['body']['pending_lineage'] is not None or r['body']['pending_symbol'] is not None:raise ValueError('successor is pending')
    lines=r['body']['lineage'];codes=[];fields=[];covariance=[[0]*D for _ in range(D)];previous=[0]*N;contacts=0
    for at,line in enumerate(lines):
        if line['occurrence']!=at or line['predecessor_state']!=(at-1 if at else None):raise ValueError('native chronology mismatch')
        code,incoming=b.input_code(line);codes.append(code)
        fields.append([v for a,c in zip(previous,incoming) for v in (a,0,c,0)])
        source=line['received_from']
        if source is not None:
            if not 0<=source<at:raise ValueError('source is not earlier standing')
            d=fields[source]+[-v for x in incoming for v in (x,0)];jd=[v for i in range(0,D,2) for v in (-d[i+1],d[i])]
            for vector in (d,jd):
                support=[(i,x) for i,x in enumerate(vector) if x]
                for i,x in support:
                    for j,y in support:covariance[i][j]+=x*y
            contacts+=1
        previous=incoming
    if r['body']['junction_covariance']['intervals']!=[[x,x] for row in covariance for x in row]+[[1,1]]:raise ValueError('full final native moment differs')
    records=r['development_records'];frames={}
    with open(r['exposure']) as stream:
        next(stream)
        for line in stream:
            frame=json.loads(line)
            if frame['sequence']>records[-1]['sequence']:break
            frames[frame['sequence']]=frame
    native_symbols=parent_contacts=0;ends={}
    for record in records:
        frame=frames[record['sequence']]
        if frame['partition']!='development' or frame['family']!=record['family'] or not record['complete']:raise ValueError('source family mismatch')
        visible={p['ordinal']:p for p in frame['views'][0]['visible_parts']}
        for part in record['parts']:
            source=visible[part['ordinal']];expected=list(source['text'].encode())+[256]
            start,end=part['native_from'],part['native_until']
            if source['pointer']!=part['pointer'] or source['kind']!=part['kind'] or codes[start:end]!=expected:raise ValueError('source material/end marker differs')
            parent=part['parent_source_occurrence']
            if parent is not None:
                family=tuple(record['parent'][k] for k in ('provider','record_group'))
                if ends.get(family)!=parent:raise ValueError('parent endpoint was not available')
                if any(not view['links'] or any(link['availability']!='prior' or tuple(link['target'][k] for k in ('provider','record_group'))!=family for link in view['links']) for view in frame['views']):raise ValueError('unfounded parent')
                parent_contacts+=1
                if lines[start]['source_contact']!='retained-anchor':raise ValueError('wrong parent source capability')
            if lines[start]['received_from']!=parent:raise ValueError('part source differs')
            for at in range(start+1,end):
                if lines[at]['received_from']!=at-1 or lines[at]['source_contact']!='emission':raise ValueError('within-part return differs')
            native_symbols+=len(expected)
        ends[tuple(record['family'][k] for k in ('provider','record_group'))]=record['native_until']-1
    if native_symbols!=r['development_native_until']:raise ValueError('unaccounted development')
    if codes[r['prompt_native_from']:r['prompt_native_until']]!=list(r['prompt'].encode())+[256]:raise ValueError('prompt differs')
    generation=r['generation'];history=r['emission_current_history'];returned=0;octets=[]
    if len(history)!=len(generation['readings']):raise ValueError('missing emitted current')
    if generation['native_from']!=r['prompt_native_until'] or generation['native_until']!=len(lines):raise ValueError('generation boundary mismatch')
    for index,(captured,reading) in enumerate(zip(history,generation['readings'])):
        at=captured['occurrence']
        if at!=reading['native']['occurrence'] or at!=generation['native_from']-1+returned:raise ValueError('emission source mismatch')
        blocks,_,_=m.unpack(captured['transport']);forward=blocks[0];masks=[0,0,0,0]
        if forward[2*N]<0:raise ValueError('negative current radius')
        for bit in range(9):
            gap=forward[4*bit+2]-forward[4*bit]
            if gap*gap>2*forward[2*N]*forward[2*N]:masks[0 if gap>0 else 1]|=1<<bit
            else:
                masks[2]|=1<<bit
                if gap==0 and forward[2*N]==0:masks[3]|=1<<bit
        if masks!=[reading['native'][k] for k in ('positive','negative','unresolved','exact_zero')]:raise ValueError('differential current receiver differs')
        disposition=reading['disposition'];kind=disposition['kind']
        if kind=='symbol':
            value=256 if disposition['symbol']['kind']=='end-part' else disposition['symbol']['value']
            if masks[2] or masks[0]!=value or value>256 or codes[at+1]!=value or lines[at+1]['received_from']!=at:raise ValueError('self-return does not match actual current')
            returned+=1
            if value<256:octets.append(value)
        elif kind=='reserved':
            if index!=len(history)-1:raise ValueError('continued past reserved current')
            if masks[2] or masks[0]<=256 or masks[0]!=disposition['codeword']:raise ValueError('reserved codeword differs')
        elif kind=='open':
            if index!=len(history)-1:raise ValueError('continued past open current')
            if not masks[2]:raise ValueError('false open current')
        else:raise ValueError('unknown material receiver result')
    if octets!=generation['emitted_octets'] or generation['native_until']-generation['native_from']!=returned:raise ValueError('emission extent differs')
    try: text=bytes(octets).decode('utf-8');text_error=None
    except UnicodeDecodeError as error: text=None;text_error=str(error)
    return {'truth_status':'established-bounded','evidence_tags':['computational-witness','measured'],
        'development_families':len(records),'development_symbols':native_symbols,'parent_contacts':parent_contacts,
        'native_occurrences':len(lines),'full_final_moment_contacts':contacts,'emission_current_receivers':len(history),
        'self_returns':returned,'emitted_octets':octets,'utf8':text,'utf8_error':text_error,'disposition':generation['disposition'],
        'historical_coefficient_certificate_claim':False,'native_model_or_update_executed_by_observer':False,
        'language_quality_established':False}


def main():
    if len(sys.argv)!=4 or sys.argv[2]!='--output':raise SystemExit('usage: inspect_material_exposure.py REPORT --output NEW.json')
    result=inspect(json.loads(Path(sys.argv[1]).read_text()))
    with os.fdopen(os.open(sys.argv[3],os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600),'w') as stream:json.dump(result,stream,indent=2);stream.write('\n')
    print(json.dumps(result))


if __name__=='__main__':main()
