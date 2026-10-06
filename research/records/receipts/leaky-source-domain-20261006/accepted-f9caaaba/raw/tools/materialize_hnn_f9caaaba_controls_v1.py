"""Seal source-bound controls; this prepares data and never launches a job."""
import hashlib
import json
from pathlib import Path

R = Path(__file__).resolve().parent
Q = R / 'hnn-material-f9caaaba-20261006'
BUILD = 'hnn-material-f9caaaba-host-cuda-link-20261006-v1'

def read(p):
    return json.loads(Path(p).read_text())

def pin(p):
    data = Path(p).read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def save(p, d):
    p = Path(p)
    assert not p.exists(), p
    p.write_text(json.dumps(d, indent=2) + '\n')

assert read(R / (BUILD + '.acceptance.json'))['passed']
assert read(R / (BUILD + '.release.json'))['quiescence_confirmed']
snapshot = read(Q / 'SOURCE_SNAPSHOT.v1.json')
source = Path(snapshot['source_root'])
request_path = Path(snapshot['owner_request'])
assert pin(request_path) == snapshot['owner_request_pin']
request = read(request_path)
assert request['source_commit'] == snapshot['source_commit']
seal = read(R / (BUILD + '.input_seal.json'))
assert seal['cwd'] == str(source)
for relative, expected in snapshot['source_inputs'].items():
    p = source / relative
    assert pin(p) == expected
    # The unchanged Lean owner is preserved independently, not compiled by Cargo.
    if p.suffix != '.lean':
        assert seal['inputs'][str(p)] == expected, p

artifacts = []
for line in (R / (BUILD + '.stdout')).read_text().splitlines():
    try:
        d = json.loads(line)
    except ValueError:
        continue
    if d.get('reason') != 'compiler-artifact' or 'holonics' not in d.get('package_id', ''):
        continue
    assert d['fresh'] is False, d
    assert d['target']['src_path'].startswith(str(source) + '/'), d
    if d.get('executable'):
        d['executable_pin'] = pin(d['executable'])
    artifacts.append(d)

executables = {
    d['target']['name']: d for d in artifacts
    if d.get('executable') and d['profile']['test'] and d['target']['kind'] != ['example']
}
for name in ['holonics', 'ranged_capacity', 'source_entrance']:
    assert name in executables
old = read(R / 'hnn-material-18968dc9-20261006/COMPILED_ARTIFACTS.v1.json')
old_binary = R / 'hnn-material-18968dc9-20261006/cache-v2/debug/deps/holonics-70b68d2f7e1f6408'
assert executables['holonics']['executable_pin'] != pin(old_binary)
manifest_path = Q / 'COMPILED_ARTIFACTS.v1.json'
save(manifest_path, {'source_commit': snapshot['source_commit'], 'build_label': BUILD,
    'all_local_artifacts_fresh_false': True, 'artifacts': artifacts})
binding = Q / 'COMPILE_SOURCE_BINDING.v1.json'
save(binding, {'passed': True, 'source_commit': snapshot['source_commit'],
    'all_native_source_inputs_match_build_seal': True,
    'all_local_artifacts_fresh_false': True,
    'new_holonics_executable_pin': executables['holonics']['executable_pin'],
    'prior_18968dc9_holonics_executable_pin': pin(old_binary),
    'new_holonics_executable_differs': True,
    'compiled_artifacts': pin(manifest_path), 'build_input_seal': pin(R / (BUILD + '.input_seal.json'))})

template = read(R / 'hnn-material-894c5d98-control-group1-20261006-v2.config.json')
groups = request['runtime_groups']
assert len(groups) == 8 and sum(g['expected_tests'] for g in groups) == 18
for n, group in enumerate(groups, 1):
    c = dict(template)
    label = f'hnn-material-f9caaaba-control-group{n}-20261006-v1'
    binary_name = 'ranged_capacity' if n == 4 else 'source_entrance' if n == 5 else 'holonics'
    binary = executables[binary_name]['executable']
    c.update(label=label, scope_unit='holonics-prune-admission-' + label,
        cwd=str(source), scope=f'Exact f9caaaba source-bound control group {n}; bounded development read counted once; no scientific run.',
        source_base=snapshot['source_base'], source_commit=snapshot['source_commit'],
        expected_test_count=group['expected_tests'], input_directories=[],
        argv=template['argv'][:7] + [binary] + group['arguments'],
        allocation_basis={'existing_fixed_development_wall_ns': 16000000000,
            'same_caps_no_raise': True, 'bounded_operands': group.get('bounded_operands'),
            'largest_matching_prior_wall_ns': group.get('prior_wall_ns'),
            'new_first_development_read': group.get('new_control_measured_projection_required_before_acceptance', False),
            'count_this_matching_development_read_once': True,
            'total_unique_candidate_controls': 18,
            'old17control_acceptance_independent': True})
    c.pop('queue_wrapper_correction', None)
    paths = [Path(binary), Q / 'SOURCE_SNAPSHOT.v1.json', manifest_path, binding, request_path]
    paths += [R / (BUILD + '.' + suffix) for suffix in ['config.json', 'acceptance.json', 'release.json', 'input_seal.json']]
    paths += [R / n for n in ['final_stage.py', 'leased_stage_v2.py', 'bounded_stage_v1.py']]
    paths += [Path('/usr/bin/env')]
    paths += [source / relative for relative in snapshot['source_inputs']]
    c['inputs'] = [str(p) for p in paths]
    c['expected_inputs'] = {str(p): pin(p) for p in paths}
    save(R / (label + '.config.json'), c)
print(json.dumps({'source_binding_passed': True, 'runtime_groups': 8,
    'expected_total_tests': 18, 'new_executable': executables['holonics']['executable_pin']}))
