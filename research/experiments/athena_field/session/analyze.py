"""Exterior task receiver: exact output comparisons and scoped process/timing summaries."""
import json, pathlib, statistics
from fractions import Fraction
base=pathlib.Path(__file__).resolve().parent
cases=json.loads((base/'held-out.json').read_text())
def integer(x): return x[0]*sum(v<<(32*i) for i,v in enumerate(x[1]))
def rational(x): return Fraction(integer(x[0]),integer(x[1]))
def events(path): return [json.loads(line) for line in path.read_text().splitlines()]
def quantiles(values):
    values=sorted(values)
    return {'count':len(values),'p50_us':statistics.median(values),'p95_us':values[min(len(values)-1,(95*len(values)+99)//100-1)],'max_us':max(values)}
result={'task':'joint contextual word correction','alphabet':['red','blue','green'],'section_symbols':2,'context_symbols':2,
        'development':'54 distinct off-diagonal requests over nine ordered correction contexts, eight passes and two resumed development comparisons; 434 actual targets total',
        'evaluation_scope':'27 diagonal requests excluded from model updates; used as recombination validation during iteration, not an untouched final benchmark',
        'runs':{}}
for name in ['initial','continued']:
    run=base/name; rows=events(run/'evaluation-events.jsonl'); predictions=[r['value'] for r in rows if r['event']=='field-request']
    assert len(predictions)==len(cases)
    assert not any('refus' in r['event'] or r['value'].get('status')=='committed-receiver-refused' for r in rows)
    readings=[]
    for case,got in zip(cases,predictions):
        readings.append({**case,'generated':got['text'],'correct':got['text']==case['target'],
                         'required_edit':case['request']!=case['target'],
                         'radius':str(rational(got['generated']['boundary']['radius'])),
                         'all_symbol_margins_robust':all(s['robust'] for s in got['selections'])})
    training=events(run/'events.jsonl')
    assert not any('refus' in r['event'] or r['value'].get('status')=='committed-receiver-refused' for r in training)
    result['runs'][name]={'correct':sum(r['correct'] for r in readings),'cases':len(readings),
        'edits_correct':sum(r['correct'] and r['required_edit'] for r in readings),'edit_cases':sum(r['required_edit'] for r in readings),
        'maximum_output_radius':str(max(Fraction(r['radius']) for r in readings)),
        'maximum_output_radius_decimal':float(max(Fraction(r['radius']) for r in readings)),
        'generation':quantiles([r['value']['generation_us'] for r in training if r['event']=='field-request']),
        'target_update':quantiles([r['value']['elapsed_us'] for r in training if r['event']=='field-observation']),
        'process':json.loads((run/'process.json').read_text()),'evaluation_process':json.loads((run/'evaluation-process.json').read_text()),
        'outputs':readings}
committed=[r['value'] for r in events(base/'continued/committed-events.jsonl') if r['event']=='field-request']
reopened=[r['value'] for r in events(base/'continued/reopen-events.jsonl') if r['event']=='field-request'][0]
assert len(committed)==28
for key in ['generated','text','symbols','selections','producing_epoch']:
    assert committed[-1][key]==reopened[key],key
result['continuing_evaluation']={'correct':sum(c['target']==v['text'] for c,v in zip(cases,committed[:27])),
    'cases':27,'material_targets':0,'exact_endpoint_reopen':True,'endpoint_text':reopened['text'],
    'process':json.loads((base/'continued/committed-process.json').read_text()),
    'reopen_process':json.loads((base/'continued/reopen-process.json').read_text())}
(base/'results.json').write_text(json.dumps(result,indent=2)+'\n')
for name,r in result['runs'].items():
    print(name,{k:v for k,v in r.items() if k not in ['outputs','process','evaluation_process']})
