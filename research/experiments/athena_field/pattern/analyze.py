"""Exterior receivers for the actual field application outputs; no native learner here."""
import json, pathlib, statistics
from fractions import Fraction
root=pathlib.Path(__file__).resolve().parent
expected=json.loads((root/'expected.json').read_text())
def rows(name):return [json.loads(s) for s in (root/'run'/name).read_text().splitlines()]
def integer(x):return x[0]*sum(v<<(32*i) for i,v in enumerate(x[1]))
def rational(x):return Fraction(integer(x[0]),integer(x[1]))
def timing(values):
 values=sorted(values)
 return {'count':len(values),'p50_us':statistics.median(values),'p95_us':values[(95*len(values)+99)//100-1],'max_us':max(values)}
outputs=rows('evaluation-events.jsonl')
assert not any('refus' in r['event'] or r['value'].get('status') for r in outputs)
outputs=[r['value'] for r in outputs if r['event']=='field-request']
result={'scope':'single learned coupled-field refinement with an affine held receiver; authored partial-pattern data',
        'source_chart':'joint-regions','realized_extents':{'field_nodes':4,'incoming_complex_coordinates':12,'condition_complex_coordinates':9,'reaction_complex_features':129},
        'development_targets':97,'development_unique_cases':24,'groups':{}}
at=0
for name in ['withheld_equal','composition_controls','shorter_output_controls']:
 cases=expected['evaluation'][name];group=[]
 assert len(outputs[at:at+len(cases)])==len(cases)
 for case,out in zip(cases,outputs[at:at+len(cases)]):
  values=out['text'].split();target=case['target'].split();held=[];inferred=[]
  assert len(values)==len(target)
  for i,(value,want) in enumerate(zip(values,target)):
   if i<len(case['partial']) and case['partial'][i] is not None:held.append(value==case['partial'][i])
   else:inferred.append(value==want)
  group.append({'partial':case['partial'],'context':case['context'],'target':case['target'],'received':out['text'],
     'correct':values==target,'generated_correct':sum(inferred),'generated_count':len(inferred),
     'held_correct':sum(held),'held_count':len(held),'radius':str(rational(out['generated']['received_boundary']['radius'])),
     'all_margins_robust':all(s['robust'] for s in out['selections'])})
 at+=len(cases)
 result['groups'][name]={'cases':len(group),'correct':sum(v['correct'] for v in group),
   'generated_correct':sum(v['generated_correct'] for v in group),'generated_count':sum(v['generated_count'] for v in group),
   'held_correct':sum(v['held_correct'] for v in group),'held_count':sum(v['held_count'] for v in group),'outputs':group}
assert at==len(outputs)
development=rows('development-events.jsonl')
assert not any('refus' in r['event'] or r['value'].get('status') for r in development)
result['generation']=timing([r['value']['generation_us'] for r in development if r['event']=='field-request'])
result['target_update']=timing([r['value']['elapsed_us'] for r in development if r['event']=='field-observation'])
result['max_received_radius']=str(max(rational(o['generated']['received_boundary']['radius']) for o in outputs))
continuing=rows('continuing-events.jsonl')
assert not any('refus' in r['event'] or r['value'].get('status') for r in continuing)
assert not any(r['event']=='field-observation' for r in continuing)
continuing=[r['value'] for r in continuing if r['event']=='field-request']
cases=[c for name in result['groups'] for c in expected['evaluation'][name]]
assert len(continuing)==len(cases)+1
assert all(o['committed'] for o in continuing[:-1]) and not continuing[-1]['committed']
result['continuing']={'cases':len(cases),'correct':sum(o['text']==c['target'] for o,c in zip(continuing,cases)),
                     'target_updates':0,'endpoint_text':continuing[-1]['text']}
reopened=rows('reopen-events.jsonl')
assert len(reopened)==1 and reopened[0]['event']=='field-request'
keys=['generated','text','symbols','selections','producing_epoch','output_symbols','observed_regions']
assert all(continuing[-1][k]==reopened[0]['value'][k] for k in keys)
result['reopen']={'exact_endpoint_match':True,'compared_fields':keys}
legacy=[json.loads(s) for s in (root/'checks'/'legacy-events.jsonl').read_text().splitlines()]
assert len(legacy)==1 and legacy[0]['event']=='field-request' and legacy[0]['value']['text']=='blue blue'
result['legacy_session_v1']={'text':legacy[0]['value']['text'],'expected':'blue blue','correct':True}
for name in ['development','evaluation','continuing','reopen']:
 result[name+'_process']=json.loads((root/'run'/f'{name}-process.json').read_text())
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
for name,g in result['groups'].items():print(name,{k:v for k,v in g.items() if k!='outputs'})
print('generation',result['generation'],'update',result['target_update'],'radius',result['max_received_radius'])
