#!/usr/bin/env python3
"""Shared exterior consequence receivers over existing public HNN operations.

No learner, training-answer router, aggregate intelligence score, or release gate lives here.
Recorded evidence and fresh execution are explicitly different modes. Source suites retain
separate histories and consumers. Add an adapter here when an actual application can consume
its source, rather than founding another benchmark for each implementation increment.
"""
from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import subprocess

import benchmark

ROOT = Path(__file__).resolve().parents[3]
FIELD = ROOT / 'research/experiments/athena_field/pattern'
SHARED = ROOT / 'research/experiments/athena_field/shared'
MATH = ROOT / 'research/experiments/contextual_prediction_release'
LEGACY_CODEC = 'utf8-nibbles'
INCIDENT_CODEC = 'unicode-scalars'
INCIDENT_SOURCE_CHART = 'incident-field'


def resolve_codec(explicit, *metadata):
    declared = []
    for value in metadata:
        if not isinstance(value, dict):
            continue
        if value.get('codec'):
            declared.append(value['codec'])
        chart = value.get('source_chart') or value.get('native_source_chart')
        if chart == 'geometric-regions':
            declared.append(LEGACY_CODEC)
        elif chart == INCIDENT_SOURCE_CHART:
            declared.append(INCIDENT_CODEC)
    if explicit:
        if explicit not in (LEGACY_CODEC, INCIDENT_CODEC):
            raise ValueError(f'unsupported codec mode: {explicit}')
        if declared and any(mode != explicit for mode in declared):
            raise ValueError('explicit codec conflicts with declared episode/result metadata')
        return explicit
    if not declared or any(mode != declared[0] for mode in declared):
        raise ValueError('episode receiver codec must be declared; byte shape is not a mode selector')
    return declared[0]


def load_lines(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def rat(value):
    if isinstance(value, dict):
        return Q(int(value['numerator']), int(value['denominator']))
    def integer(words):
        return words[0] * sum(v << (32 * i) for i, v in enumerate(words[1]))
    return Q(integer(value[0]), integer(value[1]))


def check_events(events, count, event):
    if len(events) != count:
        raise ValueError(f'expected {count} {event} records, received {len(events)}')
    sequences = [item['sequence'] for item in events]
    if any(b != a + 1 for a, b in zip(sequences, sequences[1:])):
        raise ValueError('stream sequence is not contiguous')
    if any(item.get('event') != event for item in events):
        raise ValueError('an operation refused or returned a different event')
    return [item['value'] for item in events]


def field_cases():
    groups = json.loads((FIELD / 'expected.json').read_text())['evaluation']
    return [(family, case) for family in ('withheld_equal', 'composition_controls', 'shorter_output_controls') for case in groups[family]]


def check_field(events, cases=None):
    cases = field_cases() if cases is None else cases
    values = check_events(events, len(cases), 'field-request')
    report = {'consumer': 'NativeFieldSession / constituted field',
              'supplied': 'trained D/M, partial symbol regions, context region and receiving mask',
              'inferred': 'free region currents and their simultaneous symbol faces',
              'scope': 'declared finite symbol chart; supplied values are not inferred values',
              'families': {}}
    for (family, case), value in zip(cases, values):
        target = case['target'].split()
        observed = {i: v for i, v in enumerate(case['partial']) if v is not None and i < len(target)}
        # Output length errors count against every missing coordinate; never truncate with zip.
        received = value['symbols']
        missing = [i for i in range(len(target)) if i not in observed]
        correct = lambda i, wanted: i < len(received) and received[i] == wanted
        result = {'source': case['partial'], 'context': case['context'],
                  'expected': target, 'received': received, 'text': value['text'],
                  'complete_correct': received == target and value['text'] == case['target'],
                  'presentation_agrees_with_symbols': value['text'] == ' '.join(received),
                  'inferred_correct': sum(correct(i, target[i]) for i in missing),
                  'inferred_count': len(missing),
                  'supplied_preserved': sum(correct(i, v) for i, v in observed.items()),
                  'supplied_count': len(observed),
                  'radius': str(rat(value['generated']['received_boundary']['radius'])),
                  'selections': value['selections']}
        report['families'].setdefault(family, []).append(result)
    return report


def check_shared(report=None):
    """The complete-source family: one withheld source generated in one joint section.

    Its prepared inputs are a private conversation/repository episode and repository documents,
    so this receiver consumes the experiment's published aggregate rather than re-executing it,
    and no text passes through here. It refuses a withheld-position count that arrives without
    its content-free comparators, and a family whose receiving extent or supplied positions were
    not preserved, because those are the conditions under which the count means anything.
    """
    value = json.loads((SHARED / 'results.json').read_text()) if report is None else report
    result = {'consumer': 'NativeFieldSession / shared-regions complete source',
              'supplied': 'complete source observations and every unmasked byte position of the withheld source',
              'inferred': 'the withheld byte positions, generated together in one joint section',
              'scope': 'recorded aggregate over a declared bounded prefix; the prepared inputs are private',
              'execution': 'recorded only: this family has no fresh-execution profile, because re-running it would read private material',
              'development': value['development'], 'families': []}
    for family in value['validation']['families']:
        comparators = ('most_frequent_byte_predictor_correct', 'copy_previous_byte_predictor_correct')
        if any(key not in family for key in comparators):
            raise ValueError('a withheld-position count must arrive beside its content-free comparators')
        if not family['extent_agrees'] or family['supplied_preserved'] != family['supplied_positions']:
            raise ValueError('the receiving extent or a supplied position was not preserved')
        result['families'].append({
            'source': family['source'], 'source_bytes': family['source_bytes'],
            'inferred_count': family['withheld_positions'], 'inferred_correct': family['withheld_correct'],
            'inferred_symbol_count': family['withheld_nibble_positions'],
            'inferred_symbol_correct': family['withheld_nibbles_correct'],
            'supplied_count': family['supplied_positions'], 'supplied_preserved': family['supplied_preserved'],
            'decodes_as_utf8': family['decodes_as_utf8'], 'radius': family['selection_bound'],
            'content_free_comparators': {key: family[key] for key in comparators}})
    return result


def factor_tensor(factors):
    """Reconstruct coefficients from returned factors, independently of tensor_image."""
    left = [[rat(x) for x in row] for row in factors['left_forms']]
    right = [[rat(x) for x in row] for row in factors['right_forms']]
    weights = [[rat(x) for x in row] for row in factors['receiver_family']['particular']]
    rank = factors['products']
    n, m = factors['left_extent'], factors['right_extent']
    if len(left) != rank or len(right) != rank or any(len(r) != n for r in left) or any(len(r) != m for r in right) or any(len(r) != rank for r in weights):
        raise ValueError('factor extent mismatch')
    return [[sum(row[k] * left[k][i] * right[k][j] for k in range(rank))
             for i in range(n) for j in range(m)] for row in weights]


def enclosure_difference(output, expected):
    center = output['center']
    if len(center) != len(expected):
        raise ValueError('enclosure output extent mismatch')
    radius = rat(output['radius'])
    if radius < 0:
        raise ValueError('negative radius')
    difference = [(rat(z['real']) - real, rat(z['imaginary']) - imaginary)
                  for z, (real, imaginary) in zip(center, expected)]
    squared = sum(a*a + b*b for a, b in difference)
    return {'contains_reference': squared <= radius*radius,
            'center_minus_reference': [[str(a), str(b)] for a, b in difference],
            'squared_difference': str(squared), 'radius': str(radius)}


def check_math(events, requests=None):
    requests = load_lines(MATH / 'requests.jsonl') if requests is None else requests
    values = check_events(events, len(requests), 'mathematical-return')
    report = {'consumer': 'NativeMathematicalSession',
              'supplied': 'source/condition maps, four observations with unit prior, target tensors and permitted factor forms',
              'inferred': 'normal coefficients; complex-product factorization and recurrence power',
              'scope': 'explicit supplied maps; exact solver construction is inference, independent of text reception',
              'normal': [], 'algebra': []}
    for request, value in zip(requests, values):
        r = request['command']['request']; op = r['operation']
        if op == 'predict-section' and not r['retain_prediction']:
            x = [rat(v) for v in r['preparation']['values']]
            a, ai, b, bi, h, hi = x
            # Reference WH=B after the four specified observations, including the unit prior.
            dr, di = a-b, ai-bi
            pr, pi = h*dr-hi*di, h*di+hi*dr
            expected = [((a+b+pr)/3, (ai+bi+pi)/3), ((a+b-pr)/3, (ai+bi-pi)/3)]
            result = enclosure_difference(value['output'], expected)
            result.update({'preparation': [str(z) for z in x], 'observations': value['observations'],
                           'normal_reference': [[str(a), str(b)] for a,b in expected]})
            if h in (Q(-1), Q(1)) and hi == 0:
                target = [(a,ai),(b,bi)] if h == 1 else [(b,bi),(a,ai)]
                result['unregularized_exchange'] = enclosure_difference(value['output'], target)
            report['normal'].append(result)
        elif op == 'construct-bilinear':
            target = [[rat(x) for x in row] for row in r['target']['coefficients']]
            actual = factor_tensor(value['factors'])
            report['algebra'].append({'operation': op, 'all_coefficients_equal': actual == target,
                'products': value['factors']['products'],
                'scope': 'coefficient identity for every input in the supplied rational bilinear domain',
                'coefficients': [[str(x) for x in row] for row in actual]})
        elif op in ('apply', 'read-product'):
            expected_by_owner = {2: [Q(337,120),Q(-3,4)], 3: [Q(247,120),Q(427,120)], 5: [Q(-11,12),Q(-5,12)]}
            expected = expected_by_owner[r['operator']]
            actual = list(map(rat, value['output']))
            report['algebra'].append({'operation': op, 'operator': r['operator'],
                'expected': list(map(str,expected)), 'received': list(map(str,actual)),
                'exact': actual == expected,
                'source_products_recomputed': value['source_products_recomputed']})
    report['distinct_normal_preparations'] = len({tuple(r['preparation']) for r in report['normal']})
    report['normal_query_count'] = len(report['normal'])
    return report


def process_case(name, command, requests, output):
    payload = ''.join(json.dumps(r)+'\n' for r in requests)
    (output / f'{name}-requests.jsonl').write_text(payload)
    result, wall, resources = benchmark.measured_process(command, payload)
    (output / f'{name}-events.jsonl').write_text(result.stdout)
    (output / f'{name}-stderr.txt').write_text(result.stderr)
    record = {'command': command, 'wall_ns': wall, 'process_resources': resources, 'exit_code': result.returncode,
              'clock_scope': 'fresh process with current CUDA cache; outer wall and child resources separate'}
    if result.returncode:
        return None, record
    return [json.loads(line) for line in result.stdout.splitlines() if line.strip()], record


def evaluate(mode, output, binary):
    output.mkdir(parents=True, exist_ok=False)
    result = {'schema': 'holonics.consequence-evaluation.v1', 'mode': mode,
              'aggregate_intelligence_score': None, 'sources': {}, 'workloads': {},
              'application_target': {'material': 'refined conversation exposure and repository sources at declared revisions',
                  'contract': 'docs/ATHENA_EVALUATION.md',
                  'status': 'one bounded complete-source run exists (the shared workload below); these mechanism populations still do not measure the application target, and whole episodes and actual constraints remain the contract',
                  'automatic_gold_from_assistant': False}}
    # The shared family is recorded in both modes: its prepared inputs are private, so a fresh
    # execution belongs to its own experiment, not to this public receiver.
    result['sources']['shared'] = str((SHARED / 'results.json').relative_to(ROOT))
    try:
        result['workloads']['shared'] = check_shared()
    except (ValueError, KeyError, TypeError, IndexError, OSError) as error:
        result['workloads']['shared'] = {'error': str(error)}
    if mode == 'recorded':
        field = [r for r in load_lines(FIELD/'run/evaluation-events.jsonl') if r['event']=='field-request']
        math = load_lines(MATH/'responses.jsonl')
        result['sources'] = {'field': str((FIELD/'run/evaluation-events.jsonl').relative_to(ROOT)),
                             'math': str((MATH/'responses.jsonl').relative_to(ROOT))}
    else:
        result['revision'] = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        result['binary_sha256'] = hashlib.sha256(binary.read_bytes()).hexdigest()
        field_requests = [r for r in load_lines(FIELD/'evaluation.jsonl') if r['command']['action']=='field-request']
        if any(r['command']['request']['commit'] or r['command']['request']['retain_comparison'] for r in field_requests):
            raise ValueError('evaluation-only field profile must not update or retain target comparisons')
        field, result['sources']['field'] = process_case('field', [str(binary),'--format','jsonl','hna','field-session',
            '--resume',str(FIELD/'run/trained.session'),'--input','-','--checkpoint',str(output/'field.session')],field_requests,output)
        math, result['sources']['math'] = process_case('math', [str(binary),'--format','jsonl','hna','mathematical-session','--input','-'],load_lines(MATH/'requests.jsonl'),output)
    for name, events, receiver in [('field',field,check_field),('math',math,check_math)]:
        try:
            if events is None: raise ValueError('native process failed; inspect saved stderr')
            result['workloads'][name] = receiver(events)
        except (ValueError,KeyError,TypeError,IndexError) as error:
            result['workloads'][name] = {'error': str(error)}
    (output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def assess_legacy_episode(episode, generated, output):
    """Receive one new native result beside the separate historical assessment, with no gold substitution."""
    source=json.loads((episode/'input.json').read_text())
    assessment=json.loads((episode/'assessment.json').read_text())
    run=json.loads(generated.read_text())
    generated_sha256=hashlib.sha256(generated.read_bytes()).hexdigest()
    request_id=source['request']['id']
    if assessment['request_event']!=request_id or run['request_event']!=request_id:
        raise ValueError('source, assessment and new run name different requests')
    if source.get('candidate_or_later_return_included') is not False or assessment.get('assistant_is_gold') is not False:
        raise ValueError('episode does not preserve its source/assessment boundary')
    if run.get('schema')!='holonics.geometric-episode-run.v1' or run.get('codec')!='utf8-nibbles' or run.get('material_update') is not False:
        raise ValueError('this receiver expects read-only native nibble episode output')
    value=run['native_value']
    if not isinstance(value, dict) or value.get('schema')!='org.holonics.hna.field-section.v1':
        raise ValueError('generated result does not carry a public field-section value')
    if value.get('source_chart')!='geometric-regions':
        raise ValueError('generated result does not carry the geometric source chart')
    request=''.join(part['text'] for part in source['request']['parts']).encode()
    raw_output_bytes=value.get('output_bytes')
    if not isinstance(raw_output_bytes, list) or any(not isinstance(byte, int) or not 0 <= byte <= 255 for byte in raw_output_bytes):
        raise ValueError('generated output bytes are not an octet list')
    output_bytes=bytes(raw_output_bytes)
    response_symbols=run.get('response_symbols')
    if not isinstance(response_symbols, int) or response_symbols <= 0 or response_symbols % 2:
        raise ValueError('UTF-8 nibble response extent must be a positive even symbol count')
    if run.get('held_request_octets')!=len(request) or len(output_bytes)*2!=len(value.get('symbols', [])):
        raise ValueError('declared native byte/symbol receiving extent disagrees')
    if value.get('output_symbols') != len(value.get('symbols', [])) or len(value.get('selections', [])) != value.get('output_symbols'):
        raise ValueError('generated symbols and selections have different receiving extents')
    if len(output_bytes)*2!=2*len(request)+response_symbols:
        raise ValueError('generated face changed the declared response extent')
    expected_symbols=[digit for byte in output_bytes for digit in (format(byte >> 4, 'x'), format(byte & 15, 'x'))]
    if value.get('symbols')!=expected_symbols:
        raise ValueError('generated symbols disagree with the output byte carrier')
    if any(not isinstance(face, dict) or not isinstance(face.get('selected'), int) or not 0 <= face['selected'] < 16
           for face in value['selections']):
        raise ValueError('generated nibble selections are malformed')
    if [face['selected'] for face in value['selections']]!=[int(digit, 16) for digit in expected_symbols]:
        raise ValueError('generated selections disagree with the output byte carrier')
    free=output_bytes[len(request):]
    try:
        text=free.decode('utf-8'); decoded=True
        printable=sum(char.isprintable() or char in '\n\r\t' for char in text)
        characters=len(text)
    except UnicodeDecodeError:
        decoded=False;printable=None;characters=None
    try:
        output_bytes.decode('utf-8'); whole_decoded=True
    except UnicodeDecodeError:
        whole_decoded=False
    native_decode_error=value.get('decode_error')
    if whole_decoded and native_decode_error not in (None, ''):
        raise ValueError('native decode error disagrees with valid UTF-8 output')
    if not whole_decoded and not native_decode_error:
        raise ValueError('invalid UTF-8 output has no native decode error')
    judgments=assessment.get('constraint_judgments',[])
    for judgment in judgments:
        if (judgment.get('status') not in ['satisfied','contradicted','unresolved']
                or not judgment.get('source') or not judgment.get('evidence')
                or judgment.get('generated_sha256')!=generated_sha256):
            raise ValueError('a source judgment requires status, source, evidence and this generated SHA-256')
    result={'schema':'holonics.episode-consequence.v1','request_event':request_id,
        'source_scope':source['scope'],'native_source_chart':value.get('source_chart'),
        'generated_sha256':generated_sha256,
        'supplied_request_octets':len(request),'request_preserved':output_bytes[:len(request)]==request,
        'generated_octets':len(free),'generated_utf8':decoded,'generated_characters':characters,
        'printable_or_layout_characters':printable,'elapsed_us':value.get('elapsed_us'),
        'robust_free_symbol_faces':sum(face.get('robust') is True for face in value['selections'][2*len(request):]),
        'free_symbol_faces':response_symbols,
        'historical_assessment':{'recorded_candidates':len(assessment['recorded_candidates']),
            'later_observations':len(assessment['recorded_later_observations']),
            'assistant_is_gold':False,'later_observations_are_new_output_feedback':False},
        'constraint_judgments':judgments,
        'judgment_scope':'identified review testimony; encoding/extent checks alone do not assess conversation usefulness',
        'material_update':False}
    output.mkdir(parents=True,exist_ok=False,mode=0o700)
    # The result contains no message text, but its provenance remains a private episode.
    import os
    with os.fdopen(os.open(output/'result.json',os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600),'w') as file:
        json.dump(result,file,indent=2);file.write('\n')
    return result


def assess_incident_episode(episode, generated, output):
    """Receive an IncidentField Unicode/support face without applying the nibble receiver."""
    source = json.loads((episode / 'input.json').read_text())
    assessment = json.loads((episode / 'assessment.json').read_text())
    run = json.loads(generated.read_text())
    generated_sha256 = hashlib.sha256(generated.read_bytes()).hexdigest()
    request_id = source['request']['id']
    if assessment.get('request_event') != request_id or run.get('request_event') != request_id:
        raise ValueError('source, assessment and new run name different requests')
    if source.get('candidate_or_later_return_included') is not False or assessment.get('assistant_is_gold') is not False:
        raise ValueError('episode does not preserve its source/assessment boundary')
    repository_material = source.get('repository_material', [])
    if not isinstance(repository_material, list) or any(
        not isinstance(item, dict) or not isinstance(item.get('text'), str)
        for item in repository_material
    ):
        raise ValueError('incident episode must retain complete supplied repository material')
    request_parts = source['request'].get('parts') or []
    context = source.get('declared_context') or []
    if any(not isinstance(part.get('text'), str) for part in request_parts):
        raise ValueError('incident request parts must be complete text')
    if any(any(not isinstance(part.get('text'), str) for part in event.get('parts', [])) for event in context):
        raise ValueError('incident context parts must be complete text')
    request_text = ''.join(part['text'] for part in request_parts)
    value = run.get('native_value')
    if run.get('schema') != 'holonics.incident-episode-run.v1' or run.get('material_update') is not False:
        raise ValueError('incident episode result schema or material update flag is invalid')
    if not isinstance(value, dict) or value.get('schema') != 'org.holonics.hna.field-section.v1':
        raise ValueError('generated result does not carry a public incident field-section value')
    if value.get('source_chart') != INCIDENT_SOURCE_CHART:
        raise ValueError('generated result does not carry the incident-field source chart')
    revision = value.get('codec_revision')
    if (value.get('codec') != INCIDENT_CODEC or type(revision) is not int
            or not 0 <= revision < 2**64):
        raise ValueError('incident native value does not retain its Unicode codec revision')
    context_characters = sum(len(part['text']) for event in context for part in event.get('parts', []))
    repository_characters = sum(len(item['text']) for item in repository_material)
    expected_context = context_characters + repository_characters
    if (value.get('source_cells') != len(request_text) + expected_context
            or value.get('context_cells') != expected_context):
        raise ValueError('incident native source does not retain the complete request, context and repository material')
    if value.get('material_update') is not False:
        raise ValueError('incident native value must be material-read-only')
    if run.get('response_only') is False:
        raise ValueError('incident native text must be the response face only')
    if not isinstance(value.get('text'), str):
        raise ValueError('incident native value must expose response text')
    response_aperture = run.get('response_symbols')
    if not isinstance(response_aperture, int) or response_aperture <= 0:
        raise ValueError('incident response aperture must be positive')
    if value.get('response_aperture') != response_aperture:
        raise ValueError('incident value response aperture disagrees with run metadata')
    expected_total = len(request_text) + response_aperture
    if run.get('output_symbols') != expected_total or value.get('output_symbols') != expected_total:
        raise ValueError('incident output_symbols must retain request characters plus response aperture')
    support = value.get('support')
    support_selection = value.get('support_selection')
    symbols = value.get('symbols')
    selections = value.get('selections')
    codec_symbols = value.get('codec_symbols')
    if not isinstance(support, int) or not isinstance(support_selection, dict):
        raise ValueError('incident native value must retain support and support selection receipts')
    if support_selection.get('selected') != support:
        raise ValueError('incident support selection disagrees with support extent')
    if not isinstance(symbols, list) or not isinstance(selections, list) or not isinstance(codec_symbols, list):
        raise ValueError('incident Unicode symbols/selections are malformed')
    support_extent = support
    if support_extent < 0 or support_extent > response_aperture:
        raise ValueError('incident support exceeds the declared response aperture')
    if len(value['text']) != len(symbols) or len(symbols) != support_extent:
        raise ValueError('incident response text/symbol support extent disagrees')
    if value['text'] != ''.join(symbols):
        raise ValueError('incident response text disagrees with its Unicode symbols')
    if len(selections) != response_aperture:
        raise ValueError('incident selections must cover the complete response aperture')
    if any(not isinstance(face, dict) or not isinstance(face.get('selected'), int)
           for face in selections):
        raise ValueError('incident selection receipts are malformed')
    for symbol, face in zip(symbols, selections[:support_extent]):
        selected = face['selected']
        if selected < 0 or selected >= len(codec_symbols) or codec_symbols[selected] != symbol:
            raise ValueError('incident support selection does not map through codec_symbols')
    judgments = assessment.get('constraint_judgments', [])
    for judgment in judgments:
        if (judgment.get('status') not in ['satisfied', 'contradicted', 'unresolved']
                or not judgment.get('source') or not judgment.get('evidence')
                or judgment.get('generated_sha256') != generated_sha256):
            raise ValueError('a source judgment requires status, source, evidence and this generated SHA-256')
    result = {
        'schema': 'holonics.episode-consequence.v1',
        'request_event': request_id,
        'source_scope': source['scope'],
        'native_source_chart': value.get('source_chart'),
        'generated_sha256': generated_sha256,
        'supplied_request_characters': len(request_text),
        'supplied_context_characters': context_characters,
        'supplied_repository_characters': repository_characters,
        'native_source_cells': value['source_cells'],
        'codec_revision': revision,
        'response_text': value['text'],
        'support_extent': support_extent,
        'response_aperture': response_aperture,
        'output_symbols': expected_total,
        'historical_assessment': {
            'recorded_candidates': len(assessment.get('recorded_candidates', [])),
            'later_observations': len(assessment.get('recorded_later_observations', [])),
            'assistant_is_gold': False,
            'later_observations_are_new_output_feedback': False,
        },
        'constraint_judgments': judgments,
        'judgment_scope': 'identified review testimony; support/text checks do not assess conversation usefulness',
        'material_update': False,
    }
    output.mkdir(parents=True, exist_ok=False, mode=0o700)
    with os.fdopen(os.open(output / 'result.json', os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), 'w') as file:
        file.write(json.dumps(result, indent=2) + '\n')
    return result


def assess_episode(episode, generated, output, codec=None):
    source = json.loads((episode / 'input.json').read_text())
    run = json.loads(generated.read_text())
    mode = resolve_codec(codec, source, run)
    if mode == INCIDENT_CODEC:
        return assess_incident_episode(episode, generated, output)
    return assess_legacy_episode(episode, generated, output)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['recorded','run','episode'])
    parser.add_argument('--output',type=Path,required=True,help='new result directory, never overwritten')
    parser.add_argument('--binary',type=Path,default=ROOT/'target/debug/holonics')
    parser.add_argument('--episode',type=Path,help='private input.json/assessment.json directory')
    parser.add_argument('--generated',type=Path,help='new native geometric episode result')
    parser.add_argument('--codec', choices=[LEGACY_CODEC, INCIDENT_CODEC],
                        help='explicit receiver mode; otherwise use declared episode/result metadata')
    args=parser.parse_args()
    if args.mode=='episode':
        if args.episode is None or args.generated is None:parser.error('episode mode requires --episode and --generated')
        result=assess_episode(args.episode,args.generated,args.output.resolve(),args.codec)
        print(json.dumps(result));return
    result=evaluate(args.mode,args.output.resolve(),args.binary.resolve())
    # Exit means the receiver ran; per-family failures remain visible, never a global AI verdict.
    print(json.dumps({'output':str(args.output/'result.json'),'mode':args.mode,
                      'protocol_errors':{k:v['error'] for k,v in result['workloads'].items() if 'error' in v}}))


if __name__=='__main__':main()
