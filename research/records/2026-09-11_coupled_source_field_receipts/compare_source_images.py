"""Exact cold comparison of these v7 source-field checkpoints, not a native decision.

Usage: python compare_source_images.py BEFORE_DIRECTORY AFTER_DIRECTORY
This witness requires identical echelon direction bases. Different bases need a separate
change-of-basis proof; this script does not pronounce them semantically unequal.
"""
import json
import struct
import sys
from fractions import Fraction
from pathlib import Path


class Wire:
    def __init__(self, data):
        self.data = data
        self.at = 0

    def expect(self, value):
        assert self.data[self.at:self.at + len(value)] == value
        self.at += len(value)

    def blob(self):
        length = struct.unpack_from('<Q', self.data, self.at)[0]
        self.at += 8
        value = self.data[self.at:self.at + length]
        assert len(value) == length
        self.at += length
        return value

    def finish(self):
        assert self.at == len(self.data)


def checkpoint(path):
    data = path.read_bytes()
    wire = Wire(data)
    wire.expect(b'HOLONIC-NORMAL-WAVE\x07')
    parts = {'normal_bank': wire.blob(), 'coupled_header': wire.blob(), 'neighborhood': wire.blob()}
    f = Wire(wire.blob())
    f.expect(b'HOLONIC-ANCHORED-WAVE-FAMILY\x01')
    parts['family_header'] = f.blob()
    assert json.loads(parts['family_header'])['passages'] > 0
    parts['origin'] = f.blob()
    parts['anchor'] = f.blob()
    relation = json.loads(f.blob())
    parts['last_map'] = f.blob()
    parts['coverage'] = f.blob()
    f.expect(b'HOLONIC-ANCHORED-WAVE-FAMILY-END\x01')
    f.finish()
    for contact in json.loads(parts['coupled_header'])['contacts']:
        parts['contact_' + str(contact['id'])] = wire.blob()
    wire.finish()
    return data, parts, relation


def compare(before, after):
    raw_a, a, fa = checkpoint(before / 'model.wave')
    raw_b, b, fb = checkpoint(after / 'model.wave')
    equal = {key: a[key] == b[key] for key in a}
    assert a.keys() == b.keys() and all(equal.values())
    assert {k: v for k, v in fa.items() if k != 'words'} == {k: v for k, v in fb.items() if k != 'words'}
    s, q = fa['source_width'], fa['target_width']
    k = s + q
    wa, wb = fa['words'], fb['words']
    assert wa[:s] == wb[:s] and wa[k + 1:k + 4] == wb[k + 1:k + 4]
    assert wa[k] > 0 and wb[k] > 0 and wa[k + 1] != 1
    assert len(wa) == len(wb) == k + 4 + q * q
    assert wa[k + 4:] == wb[k + 4:], 'this witness requires matching direction bases'
    delta = [Fraction(wa[s + i], wa[k]) - Fraction(wb[s + i], wb[k]) for i in range(q)]
    original = list(delta)
    coefficients = []
    rank = 0
    for p in range(q):
        row = wa[k + 4 + p * q:k + 4 + (p + 1) * q]
        assert row[p] >= 0 and not any(row[:p])
        assert row[p] or not any(row)
        rank += bool(row[p])
        if not delta[p]:
            continue
        assert row[p], 'the origin difference is outside this span'
        factor = delta[p] / row[p]
        coefficients.append({'pivot': p, 'coefficient': str(factor)})
        for j in range(p, q):
            if row[j]:
                delta[j] -= factor * row[j]
    assert not any(delta)
    files = ['source-cursor.json', 'source-progress.json', 'exterior-chart.json', 'source-66-0.predictions.json']
    delivery = {name: (before / name).read_bytes() == (after / name).read_bytes() for name in files}
    assert all(delivery.values())
    return {
        'schema': 'holonics.source-field-affine-equivalence.v1',
        'scope': 'Full constrained current family for this declared source field, with all other persisted components and source witnesses unchanged. This is not universal arithmetic-aperture or performance equivalence.',
        'model_bytes_identical': raw_a == raw_b,
        'unchanged_components': equal,
        'delivery_and_prediction_files_identical': delivery,
        'affine_metadata_identical': True,
        'direction_basis_identical': True,
        'direction_rank': rank,
        'changed_origin_coordinates': sum(bool(x) for x in original),
        'origin_difference_in_span': True,
        'origin_difference_coefficients': coefficients,
        'original_anchor_identical': equal['anchor'],
        'constrained_families_equal': True,
        'before': str(before), 'after': str(after),
    }


if __name__ == '__main__':
    print(json.dumps(compare(Path(sys.argv[1]), Path(sys.argv[2])), indent=2))
