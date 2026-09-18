"""Prepare source reconstruction data; the public session alone learns and generates.

Masks depend on source addresses, never on desired symbols. Private episode text and every
result remain under ignored .local/. Historical assistant text is observed source material,
not gold advice or feedback on a new response.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
REVISION='19964c20'
TRAIN=['docs/FORMAL_FRAMEWORK.md','docs/FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md','docs/canon/THE_REALITY_OF_DIFFERENCE.md']
VALIDATE=['docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md']
SCHEMA='org.holonics.hna.stream-request.v1'


def source(path):
    return subprocess.check_output(['git','show',REVISION+':'+path],cwd=ROOT,text=True)


def request(text,phase=0):
    data=text.encode('utf-8');symbols=[f'{n:x}' for b in data for n in (b>>4,b&15)]
    missing=[i for i in range(2,len(data)-2) if i%13==phase%13]
    for i in missing:symbols[2*i]=symbols[2*i+1]=None
    return {'partial':symbols,'commit':False,'retain_comparison':False},missing


def command(action,**body):return {'schema':SCHEMA,'command':{'action':action,**body}}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--epochs',type=int,default=3);args=parser.parse_args()
    if args.epochs<=0:parser.error('epochs must be positive')
    os.umask(0o077);out=args.output.resolve();out.mkdir(parents=True,exist_ok=False,mode=0o700)
    training=[(path,source(path)) for path in TRAIN]
    validation=[(path,source(path)) for path in VALIDATE]
    episode=json.loads((ROOT/'.local/evaluations/athena-source-episode-2026-09-15/input.json').read_text())
    text='\n\n'.join([p['text'] for p in episode['repository_material']]+[p['text'] for p in episode['request']['parts'] if p.get('text')])
    validation.append(('private:prepared-conversation-repository-episode',text))
    capacity=max(len(t.encode('utf-8'))*2 for _,t in training+validation)
    spec={'symbols':[f'{i:x}' for i in range(16)],'section_symbols':capacity,'context_symbols':0,
          'region_offsets':[-2,-1,0,1,2],'source_chart':'shared-regions','codec':'utf8-nibbles','fractional_bits':48}
    (out/'spec.json').write_text(json.dumps(spec,indent=2)+'\n')
    expected=[];queries=[]
    for name,text in validation:
        req,missing=request(text,7);queries.append(command('field-request',request=req))
        expected.append({'source':name,'text':text,'bytes':list(text.encode('utf-8')),'missing_byte_positions':missing})
    (out/'validation.jsonl').write_text(''.join(json.dumps(q)+'\n' for q in queries))
    (out/'expected.json').write_text(json.dumps(expected)+'\n')
    rows=[]
    for epoch in range(args.epochs):
        for name,text in training:
            req,missing=request(text,epoch*4)
            rows.append(command('observe-field-source',request=req,text=text,step_bits=1))
    (out/'development.jsonl').write_text(''.join(json.dumps(q)+'\n' for q in rows))
    (out/'manifest.json').write_text(json.dumps({'revision':REVISION,'training_sources':TRAIN,
        'training_bytes':[len(t.encode('utf-8')) for _,t in training],'epochs':args.epochs,
        'source_observations':len(rows),'validation_sources':[p for p,_ in validation],
        'validation_bytes':[len(t.encode('utf-8')) for _,t in validation],
        'scope':'source reconstruction; validation withheld from native updates, not a general conversation judgment',
        'fixed_D':True,'native_M_update':True},indent=2)+'\n')
    print(json.dumps({'output':str(out),'capacity_nibbles':capacity,'development_observations':len(rows),
                      'training_bytes':sum(len(t.encode('utf-8')) for _,t in training),'validation_bytes':sum(len(t.encode('utf-8')) for _,t in validation)}))


if __name__=='__main__':main()
