#!/usr/bin/env python3
"""Private real-source execution through the existing HNN field-session interfaces.

A selected exposure subsequence keeps captured events/families/relations and partitions; only
its exterior delivery sequence is rebased. Recorded responses are later observations, never
input to generation. No model law or learner lives in this adapter.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
STREAM_EVENT_SCHEMA = 'org.holonics.hna.stream-event.v1'
LEGACY_CODEC = 'utf8-nibbles'
INCIDENT_CODEC = 'unicode-scalars'
INCIDENT_SOURCE_CHART = 'incident-field'


def resolve_codec(explicit, *metadata):
    """Select a declared receiver mode; never infer it from byte-shaped payloads."""
    declared = []
    for value in metadata:
        if not isinstance(value, dict):
            continue
        if value.get('codec'):
            declared.append(value['codec'])
        if value.get('source_chart') == 'geometric-regions':
            declared.append(LEGACY_CODEC)
        if value.get('source_chart') == INCIDENT_SOURCE_CHART:
            declared.append(INCIDENT_CODEC)
    if explicit:
        if explicit not in (LEGACY_CODEC, INCIDENT_CODEC):
            raise ValueError(f'unsupported codec mode: {explicit}')
        if declared and any(mode != explicit for mode in declared):
            raise ValueError('explicit codec conflicts with declared source/checkpoint metadata')
        return explicit
    if not declared or any(mode != declared[0] for mode in declared):
        raise ValueError('receiver codec must be declared explicitly or in source metadata')
    return declared[0]

def private_json(path, value):
    with os.fdopen(os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), 'w') as stream:
        json.dump(value, stream, ensure_ascii=False)
        stream.write('\n')

def select_source(source, sequences, output):
    source = source.resolve()
    wanted = set(sequences)
    frames = {}
    digest = hashlib.sha256()
    with source.open('rb') as stream:
        first = stream.readline(); digest.update(first); manifest = json.loads(first)
        for line in stream:
            digest.update(line)
            value = json.loads(line)
            if value.get('sequence') in wanted:
                frames[value['sequence']] = value
    if set(frames) != wanted or sequences != sorted(wanted):
        raise ValueError('select distinct existing sequences in their source order')
    manifest['boundary']['experimental_delivery_projection'] = json.dumps({
        'source_sha256': digest.hexdigest(), 'original_sequences': sequences,
        'scope': 'declared source subsequence; captured coordinates/relations unchanged; delivery sequence rebased',
    })
    with os.fdopen(os.open(output, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), 'w') as stream:
        stream.write(json.dumps(manifest, ensure_ascii=False)+'\n')
        for sequence, original in enumerate(sequences):
            frame = frames[original]
            frame['sequence'] = sequence
            stream.write(json.dumps(frame, ensure_ascii=False)+'\n')
    return {'source_sha256': digest.hexdigest(), 'original_sequences': sequences,
            'events': [[view['event'] for view in frames[s]['views']] for s in sequences]}

def invoke(command, output, stdin=None):
    start = time.monotonic_ns()
    returned = subprocess.run([str(v) for v in command], input=stdin, capture_output=True, text=True, cwd=ROOT)
    private_json(output, {'command': [str(v) for v in command], 'returncode': returned.returncode,
                         'wall_ns': time.monotonic_ns()-start, 'stdout': returned.stdout, 'stderr': returned.stderr})
    if returned.returncode:
        raise RuntimeError(f'native process failed; private diagnostic: {output}')
    return [json.loads(line) for line in returned.stdout.splitlines() if line.strip()]

def compact(report):
    return {key: report[key] for key in ['frames_peeked','frames_acknowledged','held_request_symbols',
            'retained_pending_at_open','context_source_lookup','outcomes','generation_us','update_us','wall_us']}

def phase_errors(report, phase, expected_frames, require_pending=False):
    """Return protocol failures without interpreting native refusal text."""
    errors = []
    outcomes = report.get('outcomes') or {}
    if report.get('frames_declared') != expected_frames:
        errors.append(f'{phase}: frames_declared={report.get("frames_declared")} expected {expected_frames}')
    if report.get('frames_peeked') != expected_frames:
        errors.append(f'{phase}: frames_peeked={report.get("frames_peeked")} expected {expected_frames}')
    if report.get('frames_acknowledged') != expected_frames:
        errors.append(f'{phase}: frames_acknowledged={report.get("frames_acknowledged")} expected {expected_frames}')
    for label in ('native-request-refused', 'native-observation-refused'):
        if outcomes.get(label, 0):
            errors.append(f'{phase}: {label}={outcomes[label]}')
    anatomy = report.get('anatomy') or {}
    pending = anatomy.get('pending_comparisons') or []
    retained = anatomy.get('retained_shared') or []
    incident = (anatomy.get('spec') or {}).get('source_chart') == INCIDENT_SOURCE_CHART
    invalid_pending = (pending != retained or anatomy.get('pending') != 1) if incident else bool(pending)
    if require_pending and (len(retained) != 1 or invalid_pending):
        errors.append(f'{phase}: expected one retained comparison at the split boundary, with its native word in incident mode')
    if require_pending and (report.get('generation_us') or {}).get('count') != 1:
        errors.append(f'{phase}: expected one actual generated request')
    if phase in ('resume', 'whole'):
        if outcomes.get('paired-and-applied', 0) != 1:
            errors.append(f'{phase}: paired-and-applied={outcomes.get("paired-and-applied", 0)} expected 1')
        if (report.get('update_us') or {}).get('count') != 1:
            errors.append(f'{phase}: update count={(report.get("update_us") or {}).get("count")} expected 1')
        if anatomy.get('pending') != 0 or pending or retained:
            errors.append(f'{phase}: pending comparison was not drained')
    return errors

def fail_phase(output, phase, report, errors, expected_frames):
    diagnostic = output / f'{phase}-phase-error.json'
    private_json(diagnostic, {
        'schema': 'holonics.geometric-exposure-phase-error.v1',
        'phase': phase,
        'expected_frames': expected_frames,
        'errors': errors,
        'report': compact(report),
    })
    raise RuntimeError(f'{phase} phase incomplete; private diagnostic: {diagnostic}')

def public_field_request(events):
    """Read exactly one public stream field-request event and its value object."""
    matches = [event for event in events
               if event.get('schema') == STREAM_EVENT_SCHEMA and event.get('event') == 'field-request']
    if len(matches) != 1:
        raise ValueError(f'expected one schema-valid field-request event, received {len(matches)}')
    value = matches[0].get('value')
    if not isinstance(value, dict):
        raise ValueError('schema-valid field-request event has no object value')
    return value

def development(args):
    if args.split < 1 or args.split >= len(args.sequences):
        raise ValueError('split must be between one and one fewer than the selected frame count')
    if args.sequences != sorted(set(args.sequences)):
        raise ValueError('sequences must be distinct and in source order')
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False, mode=0o700)
    exposure = out/'exposure.jsonl'
    source = select_source(args.source, args.sequences, exposure)
    spec = json.loads(args.spec.read_text())
    codec = resolve_codec(args.codec, spec)
    if codec == LEGACY_CODEC:
        if spec.get('source_chart') != 'geometric-regions':
            raise ValueError('UTF-8 nibble mode requires the geometric-regions source chart')
        # Independent exterior limits share the geometry's joint slot constraint, checked per request.
        capacity = len(spec['geometry']['slot_junctions'])
        spec['section_symbols'] = capacity//2*2
        spec['context_symbols'] = capacity
    else:
        if spec.get('source_chart') != INCIDENT_SOURCE_CHART:
            raise ValueError('unicode-scalars mode requires the incident-field source chart')
        incident = spec.get('incident', {})
        for key in ('local_roots', 'material_seed', 'response_aperture', 'material_owners', 'solve_steps'):
            if key not in incident:
                raise ValueError(f'incident-field spec omits required {key}')
        if incident['response_aperture'] != args.response_symbols:
            raise ValueError('declared incident support aperture differs from the exposure aperture')
    spec_path = out/'spec.json'; private_json(spec_path, spec)
    binary = ROOT/'target'/args.profile/'examples/athena_exposure_field'
    options = ['--request-bytes',args.request_bytes,'--response-symbols',args.response_symbols,
               '--context-bytes',args.context_bytes,'--step-bits',args.step_bits]
    initial = ['--exposure',exposure,'--spec',spec_path]
    split = invoke([binary,*initial,*options,'--frames',args.split,'--checkpoint',out/'pending.session',
                    '--private-diagnostic',out/'split-native-error.txt'],out/'split-process.json')[-1]
    split_errors = phase_errors(split, 'split', args.split, require_pending=True)
    if split_errors:
        fail_phase(out, 'split', split, split_errors, args.split)
    resumed = invoke([binary,'--resume',out/'pending.session',*options,'--frames',len(args.sequences)-args.split,
                      '--checkpoint',out/'resumed.session','--private-diagnostic',out/'resume-native-error.txt'],out/'resume-process.json')[-1]
    resume_errors = phase_errors(resumed, 'resume', len(args.sequences)-args.split)
    if resumed.get('retained_pending_at_open', 0) < 1:
        resume_errors.append('resume: did not open the split pending comparison')
    if resume_errors:
        fail_phase(out, 'resume', resumed, resume_errors, len(args.sequences)-args.split)
    whole = invoke([binary,*initial,*options,'--frames',len(args.sequences),'--checkpoint',out/'whole.session',
                    '--private-diagnostic',out/'whole-native-error.txt'],out/'whole-process.json')[-1]
    whole_errors = phase_errors(whole, 'whole', len(args.sequences))
    if whole_errors:
        fail_phase(out, 'whole', whole, whole_errors, len(args.sequences))
    if resumed['outcomes'].get('paired-and-applied', 0) != whole['outcomes'].get('paired-and-applied', 0):
        fail_phase(out, 'comparison', whole, ['resume and uninterrupted paired-update counts differ'], len(args.sequences))
    hashes = {name: hashlib.sha256((out/name).read_bytes()).hexdigest() for name in ['resumed.session','whole.session']}
    result = {'schema': ('holonics.incident-development-run.v1' if codec == INCIDENT_CODEC
                         else 'holonics.geometric-exposure-run.v1'),
              'codec': codec, 'source_chart': spec.get('source_chart'), 'source':source,
              'scope':'bounded real development source; fixed geometry/codec; recorded response is observed candidate',
              'aperture':{key:getattr(args,key) for key in ['request_bytes','response_symbols','context_bytes','step_bits']},
              'split':compact(split),'resumed':compact(resumed),'uninterrupted':compact(whole),
              'same_checkpoint_bytes':len(set(hashes.values()))==1,'checkpoint_sha256':hashes,
              'checkpoint_octets':(out/'whole.session').stat().st_size}
    private_json(out/'result.json',result)
    return result

def evaluation(args):
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False,mode=0o700)
    episode=json.loads(args.episode.read_text())
    text=''.join(part['text'] for part in episode['request']['parts'])
    context=[''.join(part['text'] for part in event['parts']) for event in episode['declared_context']]
    spec_path = getattr(args, 'spec', None)
    spec_metadata = json.loads(spec_path.read_text()) if spec_path else {}
    codec = resolve_codec(args.codec, episode, spec_metadata)
    if codec == INCIDENT_CODEC:
        repository_material = episode.get('repository_material', [])
        material_context = []
        for item in repository_material:
            if not isinstance(item, dict) or not isinstance(item.get('text'), str):
                raise ValueError('incident repository material must retain complete text contents')
            material_context.append(item['text'])
        request = {
            'text': text,
            'context': context + material_context,
            'output_symbols': len(text) + args.response_symbols,
            'retain_comparison': False,
            'commit': False,
        }
        wire={'schema':'org.holonics.hna.stream-request.v1','command':{'action':'field-request','request':request}}
        admission={'schema':'org.holonics.hna.stream-request.v1',
                   'command':{'action':'admit-field-source','texts':request['context']+[text]}}
        events=invoke([ROOT/'target'/args.profile/'holonics','--format','jsonl','hna','field-session','--resume',args.checkpoint,
                       '--input','-','--checkpoint',out/'after.session'],out/'process.json',
                      json.dumps(admission)+'\n'+json.dumps(wire)+'\n')
        value=public_field_request(events)
        result={'schema':'holonics.incident-episode-run.v1','request_event':episode['request']['id'],
                'codec':INCIDENT_CODEC,'source_chart':INCIDENT_SOURCE_CHART,
                'held_request_characters':len(text),'response_symbols':args.response_symbols,
                'output_symbols':len(text)+args.response_symbols,'material_update':False,
                'response_only': True,
                'native_value':value}
        private_json(out/'result.json',result)
        return {'request_event':result['request_event'],'output':str(out/'result.json'),'material_update':False,
                'codec':INCIDENT_CODEC}
    parts=[f'{n:x}' for byte in text.encode() for n in [byte>>4,byte&15]]
    request={'partial':parts+[None]*args.response_symbols,
             'output_symbols':len(parts)+args.response_symbols,'context':context,'retain_comparison':False,'commit':False}
    # The stream request syntax is the public HNN codec, not a source-conditioned answer router.
    wire={'schema':'org.holonics.hna.stream-request.v1','command':{'action':'field-request','request':request}}
    events=invoke([ROOT/'target'/args.profile/'holonics','--format','jsonl','hna','field-session','--resume',args.checkpoint,
                   '--input','-','--checkpoint',out/'after.session'],out/'process.json',json.dumps(wire)+'\n')
    value=public_field_request(events)
    result={'schema':'holonics.geometric-episode-run.v1','request_event':episode['request']['id'],
            'codec':'utf8-nibbles','held_request_octets':len(text.encode()),'response_symbols':args.response_symbols,
            'material_update':False,'native_value':value}
    private_json(out/'result.json',result)
    return {'request_event':result['request_event'],'output':str(out/'result.json'),'material_update':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);commands=p.add_subparsers(dest='mode',required=True)
    d=commands.add_parser('development');d.add_argument('--source',type=Path,required=True);d.add_argument('--spec',type=Path,required=True)
    d.add_argument('--sequences',type=int,nargs='+',required=True);d.add_argument('--split',type=int,required=True)
    d.add_argument('--request-bytes',type=int,required=True);d.add_argument('--response-symbols',type=int,required=True)
    d.add_argument('--context-bytes',type=int,required=True);d.add_argument('--step-bits',type=int,required=True)
    d.add_argument('--codec',choices=[LEGACY_CODEC, INCIDENT_CODEC])
    e=commands.add_parser('evaluation');e.add_argument('--episode',type=Path,required=True);e.add_argument('--checkpoint',type=Path,required=True)
    e.add_argument('--spec',type=Path,help='declared source/checkpoint mode metadata')
    e.add_argument('--response-symbols',type=int,required=True);e.add_argument('--codec',choices=[LEGACY_CODEC, INCIDENT_CODEC])
    for command in [d,e]:
        command.add_argument('--output',type=Path,required=True)
        command.add_argument('--profile',choices=['debug','release'],default='debug',help='built native executable profile')
    a=p.parse_args();print(json.dumps(development(a) if a.mode=='development' else evaluation(a)))
if __name__=='__main__':main()
