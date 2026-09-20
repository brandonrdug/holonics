"""Execute the prepared shared-source run through the public Workbench field session.

The caller declares the bounded development prefix and validation prefix; nothing is inferred
from a desired answer. Every event, checkpoint and derived table stays under the private output
directory, because the prepared inputs derive from private material. Only counts, extents,
timings and symbol-level correctness leave this receiver. No target text is printed or stored
outside `.local/`, and no model answer is supplied here.
"""
import argparse
import json
import os
from pathlib import Path
import statistics
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'research/experiments/native_performance_benchmark'))
import benchmark


def load_lines(path,limit=None):
    lines=[json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]
    return lines if limit is None else lines[:limit]


def quantiles(values):
    if not values:return {'count':0,'median':None,'p95':None}
    ordered=sorted(values)
    at=min(len(ordered)-1,round((len(ordered)-1)*0.95))
    return {'count':len(ordered),'median':statistics.median(ordered),'p95':ordered[at]}


def events_of(result):
    return [json.loads(line) for line in result.stdout.splitlines() if line.strip()]


def receipt_of(result):
    for line in reversed(result.stderr.splitlines()):
        if line.strip().startswith('{'):return json.loads(line)
    return None


def run(binary,args,payload,output,name):
    completed,wall,resources=benchmark.measured_process([str(binary),'--format','jsonl','hna','field-session',*args],payload)
    (output/f'{name}-events.jsonl').write_text(completed.stdout)
    (output/f'{name}-stderr.txt').write_text(completed.stderr)
    return {'exit_code':completed.returncode,'wall_ns':wall,'process_resources':resources,
            'receipt':receipt_of(completed)},events_of(completed)


def correctness(events,expected,requests):
    """Symbol-level agreement at the withheld byte positions; supplied positions are separate."""
    families=[]
    for case,request,event in zip(expected,requests,events):
        if event.get('event')!='field-request':
            families.append({'source':case['source'],'refused':True});continue
        value=event['value']
        received=value.get('output_bytes')
        reference=case['bytes'];missing=set(case['missing_byte_positions'])
        supplied=[i for i in range(len(reference)) if i not in missing]
        agree=lambda positions:sum(1 for i in positions if received is not None and i<len(received) and received[i]==reference[i])
        families.append({'source':case['source'],'refused':False,
            'source_bytes':len(reference),'received_bytes':None if received is None else len(received),
            'extent_agrees':received is not None and len(received)==len(reference),
            'withheld_positions':len(missing),'withheld_correct':agree(sorted(missing)),
            'supplied_positions':len(supplied),'supplied_preserved':agree(supplied),
            'decodes_as_utf8':value.get('decode_error') is None,
            'generated_positions':len(value.get('generated_positions') or []),
            'output_symbols':value.get('output_symbols'),
            'selection_bound':value.get('selection_bound'),
            'generation_us':value.get('generation_us'),'elapsed_us':value.get('elapsed_us')})
    return families


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True,help='prepared private input directory')
    parser.add_argument('--output',type=Path,required=True,help='new private result directory, never overwritten')
    parser.add_argument('--binary',type=Path,default=ROOT/'target/debug/holonics')
    parser.add_argument('--resume',type=Path,help='an already trained session; validation then runs in its own bounded process')
    parser.add_argument('--development',type=int,required=True,help='declared bounded prefix of observe-field-source lines')
    parser.add_argument('--validation',type=int,required=True,help='declared bounded prefix of field-request lines')
    args=parser.parse_args()
    if args.development<0 or args.validation<=0:parser.error('declare a non-negative development prefix and a positive validation prefix')
    os.umask(0o077)
    source=args.source.resolve();output=args.output.resolve()
    output.mkdir(parents=True,exist_ok=True,mode=0o700)
    development=load_lines(source/'development.jsonl',args.development)
    validation=load_lines(source/'validation.jsonl',args.validation)
    expected=json.loads((source/'expected.json').read_text())[:args.validation]
    spec=json.loads((source/'spec.json').read_text())
    result={'schema':'org.holonics.athena-shared-baseline.v1','source':str(source),
        'spec':{k:spec[k] for k in ('section_symbols','context_symbols','region_offsets','source_chart','codec','fractional_bits')},
        'declared_development_prefix':args.development,'declared_validation_prefix':args.validation,
        'available_development':len(load_lines(source/'development.jsonl')),
        'scope':'source reconstruction at a declared bounded prefix; not a conversation benchmark'}
    trained=output/'trained.session'
    if args.resume is not None:
        result['resumed']=str(args.resume.resolve());development=[]
    if development:
        payload=''.join(json.dumps(line)+'\n' for line in development)
        record,events=run(args.binary,['--source',str(source/'spec.json'),'--input','-','--checkpoint',str(trained)],payload,output,'development')
        updates=[e['value'] for e in events if e.get('event')=='field-source-observation']
        record['observations']=len(updates)
        record['refusals']=sum(1 for e in events if e.get('event')=='refused')
        record['update_us']=quantiles([v['elapsed_us'] for v in updates if 'elapsed_us' in v])
        record['rows']=[v.get('returned',{}).get('rows') for v in updates]
        result['development']=record
        resume=['--resume',str(trained)]
    elif args.resume is not None:
        resume=['--resume',str(args.resume.resolve())]
    else:
        resume=['--source',str(source/'spec.json')]
    payload=''.join(json.dumps(line)+'\n' for line in validation)
    record,events=run(args.binary,[*resume,'--input','-','--checkpoint',str(output/'validation.session')],payload,output,'validation')
    values=[e for e in events if e.get('event') in ('field-request','refused')]
    record['families']=correctness(values,expected,validation)
    record['generation_us']=quantiles([f['generation_us'] for f in record['families'] if f.get('generation_us')])
    result['validation']=record
    result['session_octets']={name:path.stat().st_size for name,path in
        (('trained',trained),('validation',output/'validation.session')) if path.exists()}
    (output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(output/'result.json'),
        'development':{k:result.get('development',{}).get(k) for k in ('exit_code','observations','refusals','update_us')},
        'validation':{'exit_code':result['validation']['exit_code'],
            'families':[{k:v for k,v in f.items() if k!='selection_bound'} for f in result['validation']['families']],
            'generation_us':result['validation']['generation_us']},
        'session_octets':result['session_octets'],
        'max_rss_kib':{k:(result.get(k,{}).get('process_resources') or {}).get('max_rss_kib') for k in ('development','validation')}}))


if __name__=='__main__':main()
