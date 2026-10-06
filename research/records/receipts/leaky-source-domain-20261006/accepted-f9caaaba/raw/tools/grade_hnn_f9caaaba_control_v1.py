"""Grade one completed source-bound control, including nonzero exact test count."""
import hashlib
import json
import re
import sys
from pathlib import Path

R = Path(__file__).resolve().parent
Q = R / 'hnn-material-f9caaaba-20261006'
n = int(sys.argv[1])
label = f'hnn-material-f9caaaba-control-group{n}-20261006-v1'

def read(s):
    return json.loads((R / (label + '.' + s)).read_text())

config = read('config.json')
acceptance = read('acceptance.json')
release = read('release.json')
final = read('final.json')
publication = read('publication.json')
seal = read('input_seal.json')
stdout = (R / (label + '.stdout')).read_text()
stderr = (R / (label + '.stderr')).read_text()
counts = re.findall(r'^test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored; (\d+) measured;', stdout, re.M)
running = re.findall(r'^running (\d+) tests?$', stdout, re.M)
expected = config['expected_test_count']
test_names = re.findall(r'^test ([A-Za-z0-9_:]+) \.\.\.', stdout, re.M)
selector = config['argv'][8]
exact = '--exact' in config['argv']
source_commit = config['source_commit']
issues = []
if not acceptance.get('passed') or not release.get('quiescence_confirmed'):
    issues.append('stage acceptance or quiescent release failed')
if counts != [(str(expected), '0', '0', '0')] or running != [str(expected)]:
    issues.append('actual executed test count does not equal sealed expected count')
if len(test_names) != expected or len(set(test_names)) != expected:
    issues.append('test names are absent or duplicated')
if any((name != selector if exact else not name.startswith(selector)) for name in test_names):
    issues.append('actual test name does not match sealed selector')
if seal['argv'] != config['argv'] or seal['cwd'] != config['cwd']:
    issues.append('executed argv or cwd differs from sealed request')
for path, expected_pin in config['expected_inputs'].items():
    data = Path(path).read_bytes()
    current_pin = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    if seal['inputs'].get(path) != expected_pin or current_pin != expected_pin:
        issues.append('source or executable input changed: ' + path)
measurement = {
    'wall_ns': final['wall_ns'], 'fixed_deadline_ns': config['projection_ns'],
    'measured_to_fixed_deadline': {'numerator': final['wall_ns'], 'denominator': config['projection_ns']},
    'aggregate_CPU_ns': final['final_CPU_ns'],
    'aggregate_CPU_limit_us': config['aggregate_cpu_limit_us'],
    'group_peak_bytes': int(final['unit_properties']['MemoryPeak']),
    'peak_child_RSS_KiB': publication['outcome'].get('peak_child_RSS_KiB'),
    'first_matching_development_read_counted_once': True,
    'subsequent_same_shape_projection_unit_upper_ns': final['wall_ns'],
}
result = {'passed': not issues, 'label': label, 'source_commit': source_commit,
    'expected_tests': expected, 'actual_test_names': test_names,
    'test_count_and_source_binding_verified': not issues,
    'quiescent': release.get('quiescence_confirmed'), 'issues': issues,
    'measurement': measurement, 'raw_stdout': str(R / (label + '.stdout')),
    'raw_stderr': str(R / (label + '.stderr')),
    'unchanged_predecessor_acceptances_remain_independent': True,
    'scientific_job': False, 'GPU_runtime': False}
out = Q / f'CONTROL_RESULT.group{n}.v1.json'
assert not out.exists(), out
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
sys.exit(0 if result['passed'] else 1)
