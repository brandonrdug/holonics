#!/usr/bin/env python3
"""Cold inspection of the declared 18-port text return and its unchanged current carriers.

This is a targeted source/current/receiver comparison, not a language-quality test or a learner.
It never supplies a symbol, numerical current or update to the native model.
"""
import json
import os
import sys
from pathlib import Path

N = 18
D = 6 * N
STRIDE = D + 1


def unpack(section):
    words = section['intervals']
    if section['rows'] != 1 or section['width'] != 12 * STRIDE or len(words) != 12 * STRIDE:
        raise ValueError('unexpected full junction report shape')
    if any(lo != hi for lo, hi in words):
        raise ValueError('packed current report is not an exact wire')
    values = []
    for i in range(len(words) // 2):
        value = ((words[2*i+1][0] & ((1 << 64)-1)) << 64) | (words[2*i][0] & ((1 << 64)-1))
        values.append(value - (1 << 128) if value >= (1 << 127) else value)
    return [values[k*STRIDE:(k+1)*STRIDE] for k in range(6)]


def input_code(lineage):
    incoming = lineage['incoming']
    if len(incoming) != N or lineage['frame'] != 0:
        raise ValueError('text inspection requires its 18-port identity-frame chart')
    values = []
    for value in incoming:
        if value['denominator'] != 1 or value['imaginary'] != 0 or value['real'] not in (0, 1):
            raise ValueError('input is outside the declared unit impulse chart')
        values.append(value['real'])
    code = 0
    for bit in range(9):
        if values[2*bit] + values[2*bit+1] != 1:
            raise ValueError('input is not one pulse per pair')
        code |= values[2*bit+1] << bit
    if code > 256:
        raise ValueError('input is a reserved codeword')
    return code, values


def compare(report, earlier, require_identical_body=True):
    if report.get('native_error') or report.get('development_error') or report.get('prompt_error'):
        raise ValueError('the native/material return refused')
    if report['body']['pending_lineage'] is not None or report['body']['pending_symbol'] is not None:
        raise ValueError('the native/application successor is pending')
    same_body = report['body'] == earlier['body']
    if (require_identical_body and not same_body) or report['generation'] != earlier['generation']:
        raise ValueError('cold current capture changed the observed body or generation')
    if not require_identical_body:
        for key in ('occurrences','lineage','pending_lineage','pending_symbol','held','relation','junction_covariance'):
            if report['body'][key] != earlier['body'][key]:
                raise ValueError(f'the numerical policy changed structural standing: {key}')
    lineages = report['body']['lineage']
    codes, arrivals, fields = [], [], []
    previous = [0] * N
    for at, lineage in enumerate(lineages):
        if lineage['occurrence'] != at or lineage['predecessor_state'] != (at-1 if at else None):
            raise ValueError('native chronology mismatch')
        code, incoming = input_code(lineage)
        codes.append(code)
        arrivals.append([entry for value in incoming for entry in (value, 0)])
        fields.append([entry for left, right in zip(previous, incoming) for entry in (left, 0, right, 0)])
        previous = incoming
    records = report['development_records']
    frames = {}
    with open(report['exposure']) as stream:
        next(stream)
        for line in stream:
            frame = json.loads(line)
            if frame['sequence'] > records[-1]['sequence']:
                break
            frames[frame['sequence']] = frame
    end_sources = {}
    material_symbols = parent_contacts = 0
    for record in records:
        frame = frames[record['sequence']]
        if frame['partition'] != 'development' or frame['family'] != record['family'] or not record['complete']:
            raise ValueError('development source/partition mismatch')
        visible = {part['ordinal']: part for part in frame['views'][0]['visible_parts']}
        for part in record['parts']:
            source = visible[part['ordinal']]
            expected = list(source['text'].encode('utf-8')) + [256]
            start, end = part['native_from'], part['native_until']
            if source['pointer'] != part['pointer'] or source['kind'] != part['kind'] or codes[start:end] != expected:
                raise ValueError('actual material or end-marker sequence mismatch')
            parent = part['parent_source_occurrence']
            if parent is not None:
                family = tuple(record['parent'][k] for k in ('provider', 'record_group'))
                if end_sources.get(family) != parent:
                    raise ValueError('parent source was not the actual earlier endpoint')
                if any(not view['links'] or any(link['availability'] != 'prior'
                    or tuple(link['target'][k] for k in ('provider', 'record_group')) != family
                    for link in view['links']) for view in frame['views']):
                    raise ValueError('native parent disagrees with source-qualified availability')
                parent_contacts += 1
            if lineages[start]['received_from'] != parent:
                raise ValueError('part-start native contact mismatch')
            if parent is not None and lineages[start]['source_contact'] != 'retained-anchor':
                raise ValueError('parent did not use shared historical standing')
            for at in range(start + 1, end):
                if lineages[at]['received_from'] != at - 1 or lineages[at]['source_contact'] != 'emission':
                    raise ValueError('within-part source link mismatch')
            material_symbols += len(expected)
        end_sources[tuple(record['family'][k] for k in ('provider', 'record_group'))] = record['native_until'] - 1
    if material_symbols != report['development_native_until']:
        raise ValueError('material aperture did not account for every native input')
    if codes[report['prompt_native_from']:report['prompt_native_until']] != list(report['prompt'].encode()) + [256]:
        raise ValueError('prompt input mismatch')
    generation = report['generation']
    currents = report['emission_current_history']
    if len(currents) != len(generation['readings']):
        raise ValueError('missing complete emission currents')
    if generation['native_from'] != report['prompt_native_until'] or generation['native_until'] != len(lineages):
        raise ValueError('generation did not continue the exact prompt successor')
    if generation['native_until'] - generation['native_from'] != len(currents):
        raise ValueError('not every observed symbol returned through one native operation')
    decoded = []
    outgoing = []
    for captured, reading in zip(currents, generation['readings']):
        at = captured['occurrence']
        if at != generation['native_from'] - 1 + len(outgoing):
            raise ValueError('generation read an old or skipped source')
        if at != reading['native']['occurrence']:
            raise ValueError('current/receiver source mismatch')
        values = unpack(captured['junction'])
        out = values[1]
        if out[D] < 0:
            raise ValueError('negative outgoing error radius')
        masks = [0, 0, 0, 0]
        for bit in range(9):
            gap = out[4*N + 4*bit + 2] - out[4*N + 4*bit]
            if gap * gap > 2 * out[D] * out[D]:
                masks[0 if gap > 0 else 1] |= 1 << bit
            else:
                masks[2] |= 1 << bit
                if gap == 0 and out[D] == 0:
                    masks[3] |= 1 << bit
        if masks != [reading['native'][key] for key in ('positive', 'negative', 'unresolved', 'exact_zero')]:
            raise ValueError('differential receiver disagrees with its complete current ball')
        if reading['disposition']['kind'] != 'symbol' or masks[2] or masks[0] > 256:
            raise ValueError('this first-return comparison expects actual emitted symbols')
        symbol = reading['disposition']['symbol']
        value = 256 if symbol['kind'] == 'end-part' else symbol['value']
        if value != masks[0]:
            raise ValueError('exterior codeword disagrees with native differential signs')
        if value < 256:
            decoded.append(value)
        if codes[at+1] != value or lineages[at+1]['received_from'] != at or lineages[at+1]['source_contact'] != 'emission':
            raise ValueError('self-emission did not return as the actual next occurrence')
        outgoing.append(out)
    if decoded != generation['emitted_octets']:
        raise ValueError('reported output changed native-emitted octets')
    if generation['disposition']['kind'] == 'interrupted' and len(currents) != report['symbol_work_limit']:
        raise ValueError('interruption disagrees with the declared work boundary')
    distinct = sum(sum((a-b)**2 for a, b in zip(left[:D], right[:D])) > (left[D]+right[D])**2
                   for left, right in zip(outgoing, outgoing[1:]))
    # Recover the actual complete moment from all recorded source/receiving maps, including
    # each separate shared-parent and self-return contact. This is a cold equality check.
    covariance = [[0] * D for _ in range(D)]
    contacts = 0
    for at, lineage in enumerate(lineages):
        source = lineage['received_from']
        if source is None:
            continue
        if not 0 <= source < at:
            raise ValueError('source is not earlier native standing')
        d = fields[source] + [-v for v in arrivals[at]]
        jd = [part for i in range(0, D, 2) for part in (-d[i+1], d[i])]
        for vector in (d, jd):
            support = [(i, value) for i, value in enumerate(vector) if value]
            for i, left in support:
                for j, right in support:
                    covariance[i][j] += left * right
        contacts += 1
    native = report['body']['junction_covariance']['intervals']
    if native != [[v, v] for row in covariance for v in row] + [[1, 1]]:
        raise ValueError('final native contact moment differs from its full actual contact population')
    return {'truth_status':'established-bounded','evidence_tags':['computational-witness','measured'],
        'complete_body_and_generation_equal_to_earlier_run':same_body,
        'generation_equal_to_earlier_run':True, 'native_occurrences':len(lineages),
        'development_symbols_checked':material_symbols,'shared_parent_contacts_checked':parent_contacts,
        'full_final_moment_contacts_checked':contacts,'emission_currents_checked':len(currents),
        'self_returns_checked':len(currents),'consecutive_disjoint_outgoing_balls':distinct,
        'consecutive_current_comparisons':max(0,len(currents)-1),'decoded_output':bytes(decoded).decode('utf-8'),
        'disposition':generation['disposition'],'native_model_or_update_executed_by_observer':False,
        'language_quality_established':False}


def main():
    if len(sys.argv) != 5 or sys.argv[3] != '--output':
        raise SystemExit('usage: inspect_text_return.py REPORT EARLIER --output NEW.json')
    result = compare(json.loads(Path(sys.argv[1]).read_text()), json.loads(Path(sys.argv[2]).read_text()))
    with os.fdopen(os.open(sys.argv[4], os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600), 'w') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
