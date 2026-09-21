import importlib.util
import json
import sys
import tempfile
import unittest
from hashlib import sha256
from pathlib import Path


QUALITY_PATH = Path(__file__).with_name('quality.py')
sys.path.insert(0, str(QUALITY_PATH.parent))
SPEC = importlib.util.spec_from_file_location('native_quality', QUALITY_PATH)
quality = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(quality)


def write_episode(root, judgment_hash=None, candidate=False):
    episode = root / 'episode'
    episode.mkdir()
    (episode / 'input.json').write_text(json.dumps({
        'schema': 'holonics.evaluation-episode-input.v1',
        'scope': 'synthetic receiver test',
        'candidate_or_later_return_included': False,
        'request': {'id': 1, 'parts': [{'text': 'A'}]},
    }) + '\n')
    (episode / 'assessment.json').write_text(json.dumps({
        'schema': 'holonics.evaluation-episode-assessment.v1',
        'request_event': 1,
        'assistant_is_gold': False,
        'recorded_candidates': [{'id': 2}] if candidate else [],
        'recorded_later_observations': [],
            'constraint_judgments': [{
            'status': 'unresolved',
            'source': 'request:1',
            'evidence': 'synthetic receiver assertion',
                'generated_sha256': judgment_hash,
            }],
    }) + '\n')
    return episode


def write_incident_episode(root):
    episode = root / 'incident-episode'
    episode.mkdir()
    (episode / 'input.json').write_text(json.dumps({
        'schema': 'holonics.evaluation-episode-input.v1',
        'scope': 'incident receiver test',
        'candidate_or_later_return_included': False,
        'request': {'id': 9, 'parts': [{'text': 'Ask'}]},
        'declared_context': [{'id': 8, 'parts': [{'text': 'Prior context'}]}],
        'repository_material': [{'commit': 'abc', 'path': 'README.md', 'text': 'material'}],
    }) + '\n')
    (episode / 'assessment.json').write_text(json.dumps({
        'schema': 'holonics.evaluation-episode-assessment.v1',
        'request_event': 9,
        'assistant_is_gold': False,
        'recorded_candidates': [],
        'recorded_later_observations': [],
        'constraint_judgments': [],
    }) + '\n')
    return episode


def write_incident_generated(root, support_extent=2):
    generated = root / 'incident-generated.json'
    codec_symbols = ['a', 'é', 'λ']
    symbols = ['é', 'λ'][:support_extent]
    selections = [{'selected': codec_symbols.index(symbol), 'robust': True}
                  for symbol in symbols]
    selections.extend([{'selected': 0, 'robust': True}] * (4 - len(selections)))
    value = {
        'schema': 'org.holonics.hna.field-section.v1',
        'source_chart': 'incident-field',
        'codec': 'unicode-scalars',
        'codec_symbols': codec_symbols,
        'codec_revision': 0,
        'source_cells': 24,
        'context_cells': 21,
        'text': ''.join(symbols),
        'output_symbols': 7,
        'symbols': symbols,
        'support': support_extent,
        'response_aperture': 4,
        'selections': selections,
        'support_selection': {'selected': support_extent, 'receipt': 'test'},
        'material_update': False,
    }
    generated.write_text(json.dumps({
        'schema': 'holonics.incident-episode-run.v1',
        'request_event': 9,
        'codec': 'unicode-scalars',
        'source_chart': 'incident-field',
        'held_request_characters': 3,
        'response_symbols': 4,
        'output_symbols': 7,
        'material_update': False,
        'native_value': value,
    }) + '\n')
    return generated


def write_generated(root, free, response_symbols=4):
    generated = root / 'generated.json'
    output = [65] + list(free)
    symbols = [digit for byte in output for digit in (format(byte >> 4, 'x'), format(byte & 15, 'x'))]
    selections = [{'selected': int(digit, 16), 'robust': True} for digit in symbols]
    try:
        bytes(free).decode('utf-8')
        decode_error = None
    except UnicodeDecodeError:
        decode_error = 'invalid utf8'
    value = {
        'schema': 'org.holonics.hna.field-section.v1',
        'source_chart': 'geometric-regions',
        'output_bytes': output,
        'output_symbols': len(symbols),
        'symbols': symbols,
        'selections': selections,
        'decode_error': decode_error,
    }
    generated.write_text(json.dumps({
        'schema': 'holonics.geometric-episode-run.v1',
        'request_event': 1,
        'codec': 'utf8-nibbles',
        'held_request_octets': 1,
        'response_symbols': response_symbols,
        'material_update': False,
        'native_value': value,
    }) + '\n')
    return generated


def bind_judgment(episode, generated):
    payload = json.loads((episode / 'assessment.json').read_text())
    payload['constraint_judgments'][0]['generated_sha256'] = sha256(generated.read_bytes()).hexdigest()
    (episode / 'assessment.json').write_text(json.dumps(payload) + '\n')


class EpisodeQualityTests(unittest.TestCase):
    def test_response_extent_mismatch_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generated = write_generated(root, b'AB', response_symbols=2)
            episode = write_episode(root)
            bind_judgment(episode, generated)
            with self.assertRaises(ValueError):
                quality.assess_episode(episode, generated, root / 'out')

    def test_request_bytes_replacement_is_reported_as_a_failed_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generated = write_generated(root, b'AB')
            payload = json.loads(generated.read_text())
            payload['native_value']['output_bytes'][0] = ord('X')
            output = payload['native_value']['output_bytes']
            symbols = [digit for byte in output for digit in (format(byte >> 4, 'x'), format(byte & 15, 'x'))]
            payload['native_value']['symbols'] = symbols
            payload['native_value']['selections'] = [{'selected': int(digit, 16), 'robust': True} for digit in symbols]
            generated.write_text(json.dumps(payload) + '\n')
            episode = write_episode(root, candidate=True)
            bind_judgment(episode, generated)
            result = quality.assess_episode(episode, generated, root / 'out')
            self.assertFalse(result['request_preserved'])

    def test_symbol_or_selection_mismatch_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generated = write_generated(root, b'AB')
            payload = json.loads(generated.read_text())
            payload['native_value']['symbols'][0] = '0'
            generated.write_text(json.dumps(payload) + '\n')
            episode = write_episode(root)
            bind_judgment(episode, generated)
            with self.assertRaises(ValueError):
                quality.assess_episode(episode, generated, root / 'out')

    def test_invalid_utf8_is_a_failed_output_face(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generated = write_generated(root, b'\xff\xfe')
            episode = write_episode(root)
            bind_judgment(episode, generated)
            result = quality.assess_episode(episode, generated, root / 'out')
            self.assertFalse(result['generated_utf8'])

    def test_stale_judgment_artifact_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generated = write_generated(root, b'AB')
            episode = write_episode(root, judgment_hash='0' * 64)
            with self.assertRaises(ValueError):
                quality.assess_episode(episode, generated, root / 'out')

    def test_incident_field_uses_response_text_and_support_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            episode = write_incident_episode(root)
            generated = write_incident_generated(root)
            result = quality.assess_episode(episode, generated, root / 'out')
            self.assertEqual(result['native_source_chart'], 'incident-field')
            self.assertEqual(result['response_text'], 'éλ')
            self.assertEqual(result['support_extent'], 2)
            self.assertNotIn('repository_material_count', result)

    def test_incident_support_must_fit_response_aperture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            episode = write_incident_episode(root)
            generated = write_incident_generated(root, support_extent=5)
            with self.assertRaises(ValueError):
                quality.assess_episode(episode, generated, root / 'out')

    def test_incident_receiver_rejects_missing_repository_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            episode = write_incident_episode(root)
            generated = write_incident_generated(root)
            payload = json.loads(generated.read_text())
            payload['native_value']['source_cells'] -= len('material')
            payload['native_value']['context_cells'] -= len('material')
            generated.write_text(json.dumps(payload) + '\n')
            with self.assertRaisesRegex(ValueError, 'complete request, context and repository'):
                quality.assess_episode(episode, generated, root / 'out')

    def test_incident_mode_is_declared_and_does_not_guess_from_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            episode = write_incident_episode(root)
            generated = write_incident_generated(root)
            payload = json.loads(generated.read_text())
            payload['native_value']['output_bytes'] = [65, 66]
            generated.write_text(json.dumps(payload) + '\n')
            result = quality.assess_episode(episode, generated, root / 'out', 'unicode-scalars')
            self.assertEqual(result['response_text'], 'éλ')


if __name__ == '__main__':
    unittest.main()
