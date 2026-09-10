"""Audit the exposed byte chart and occurrence-expanded material in a cold field report.

Reads existing evidence only; no native execution, fitting, source-text output or output attribution.
Usage: python inspect_representation.py PRIVATE_REPORT.json NEW_RECEIPT.json
"""
import argparse
import json
from pathlib import Path
import runpy


def inspect(report_path):
    document = json.loads(report_path.read_bytes())
    helper = Path(__file__).resolve().parents[2] / 'records/2026-09-09_normal_material/inspect_phase_comparison.py'
    packet = runpy.run_path(str(helper))['packet']
    records = {record['sequence']: record for record in document['development_records']}
    frames = {}
    with Path(document['exposure']).open('rb') as source:
        next(source)  # The exterior manifest, already validated by the original exposure reader.
        for line in source:
            frame = json.loads(line)
            if frame['sequence'] in records:
                frames[frame['sequence']] = frame
                if len(frames) == len(records):
                    break
    assert frames.keys() == records.keys()
    lineage = document['body']['lineage']
    restored_octets = parts = 0
    for sequence, record in records.items():
        frame = frames[sequence]
        assert frame['family'] == record['family']
        for part in record['parts']:
            actual = bytearray()
            end_seen = False
            for event in lineage[part['native_from']:part['native_until']]:
                coordinate, phase = packet(event['incoming'], document['material_target']['factor_width'])
                assert phase == ((0, 1) if part['kind'] == 'agent-text' else (1, 0))
                assert not end_seen
                if coordinate == 1 << 8:
                    end_seen = True
                else:
                    actual.append(coordinate)
            assert end_seen and len(actual) == part['source_octets']
            for view in frame['views']:
                candidates = [p for p in view['visible_parts'] if p['ordinal'] == part['ordinal']]
                assert len(candidates) == 1
                assert bytes(actual) == candidates[0]['text'].encode('utf-8')
            parts += 1
            restored_octets += len(actual)
    cut = document['development_native_until']
    operative = document['body']['operative_contacts']
    births = operative['births']
    development_births = [b for b in births if b['receiving'] < cut]
    observations = [event for event in lineage[:cut] if event['received_from'] is not None]
    assert [(b['receiving'], b['source']) for b in development_births] == [
        (event['occurrence'], event['received_from']) for event in observations]
    rows = {len(column) for column in operative['contacts']}
    assert len(rows) == 1
    root_complex_dimension = rows.pop()
    return {
        'grade': 'established-bounded', 'evidence': ['computational-witness', 'source-inspected'],
        'scope': 'Cold reported lineage and material of the existing staged continuation. Exact exposed byte recovery is checked against every captured view of its selected source parts. No claim that all current/history distinctions may be deleted; no cultivation or inference performed.',
        'source_revision': 'cf6d5b6b', 'report': str(report_path),
        'exposed_parts': parts, 'exposed_text_octets': restored_octets,
        'all_exposed_bytes_recovered_exactly_from_native_lineage': True,
        'development_occurrences': cut, 'development_contact_births': len(development_births),
        'every_source_linked_development_observation_has_a_contact_birth': True,
        'final_occurrences': document['body']['occurrences'],
        'final_contact_coordinates': len(births), 'final_contact_complex_rows': root_complex_dimension,
        'instantaneous_contact_kernel_dimension_lower_bound': max(0, len(births) - root_complex_dimension),
        'kernel_scope': 'Algebraic dimension bound for the current numerical contact matrix only. Changing contacts can expose its current kernel; this is not permission to discard it or a dynamic compression certificate.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report', type=Path)
    parser.add_argument('receipt', type=Path)
    args = parser.parse_args()
    result = inspect(args.report)
    with args.receipt.open('x') as output:
        json.dump(result, output, indent=2)
        output.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
