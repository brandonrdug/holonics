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


if __name__ == '__main__':
    unittest.main()
