"""Reconcile the archived native controls; never launch compiler or native code."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path.cwd()
dest = Path(__file__).resolve().parent
archive = root / 'research/records/receipts/pair-output-learning-20261006/native-validation-correlated-6f536ac3-v1'
validation = archive / 'VALIDATION.json'
r = json.loads(validation.read_text())
head = r['source_commit']

def pin(data):
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())

def named(name):
    hits = [v for k, v in r['artifacts'].items() if k.endswith('/' + name)]
    assert len(hits) == 1, name
    return (archive / hits[0]['copy']).read_bytes()

for name, value in r['artifacts'].items():
    assert pin((archive / value['copy']).read_bytes()) == {k: value[k] for k in ('bytes', 'sha256')}, name
s = json.loads(named('SOURCE_SNAPSHOT.v1.json'))
inputs = s['source_inputs']
assert s['source_commit'] == head and inputs == r['source_inputs']
for name, wanted in inputs.items():
    assert pin(subprocess.check_output(['git', 'show', head + ':' + name])) == wanted, name
    assert pin((Path(s['source_root']) / name).read_bytes()) == wanted, name
native = {name: value for name, value in inputs.items() if not name.startswith('lean/')}
build = 'hnn-correlated-6f536ac3-host-cuda-link-20261006-v1'
compiled = json.loads(named('COMPILED_ARTIFACTS.v1.json'))['artifacts']
cargo = [json.loads(line) for line in named(build + '.stdout').decode().splitlines() if line.startswith('{')]
local = [a for a in cargo if a.get('reason') == 'compiler-artifact' and 'path+file://' in a.get('package_id', '')]
assert len(compiled) == len(local) == 11 and all(a['fresh'] is False for a in compiled)
assert [{k: v for k, v in a.items() if k != 'executable_pin'} for a in compiled] == local
host = next(a for a in compiled if a['target']['name'] == 'holonics' and a['profile']['test'] and a.get('executable'))
assert host['executable_pin'] == r['compiled_source_binding']['new_holonics_executable_pin']
assert pin((archive / r['artifacts'][host['executable']]['copy']).read_bytes()) == host['executable_pin']

names = []
whole = bytearray()
seal_pins = {}
for run in r['runtime_results']:
    assert run['passed'] and run['quiescent'] and not run['issues']
    assert run['source_commit'] == head
    raw = named(run['label'] + '.stdout')
    actual = re.findall(r'^test (\S+) \.\.\.', raw.decode(), re.M)
    assert actual == run['actual_test_names'] and len(actual) == run['expected_tests']
    assert f"test result: ok. {len(actual)} passed; 0 failed; 0 ignored;" in raw.decode()
    names.extend(actual)
    whole.extend(raw)
    seal_pins[run['label']] = pin(named(run['label'] + '.input_seal.json'))
assert names == r['actual_test_names'] and len(names) == len(set(names)) == r['expected_and_executed_unique_tests'] == 28
assert len(r['runtime_results']) == r['runtime_groups'] == 18
repair = r['queue_namespace_filter_metadata_repair']
assert repair['original_would_select'] == 13 and repair['declared'] == 11
assert repair['explicit_skips_added'] == names[:2]
assert r['runtime_results'][4]['expected_tests'] == 11
assert all(name not in r['runtime_results'][4]['actual_test_names'] for name in names[:2])
group5 = r['runtime_results'][4]['label']
argv = json.loads(named(group5 + '.config.json'))['argv']
assert argv == json.loads(named(group5 + '.input_seal.json'))['argv']
skips = [argv[i + 1] for i, value in enumerate(argv[:-1]) if value == '--skip']
assert all(name in skips for name in names[:2])

for label in (build, *(run['label'] for run in r['runtime_results'])):
    seal = json.loads(named(label + '.input_seal.json'))['inputs']
    for name, wanted in native.items():
        assert seal[str(Path(s['source_root']) / name)] == wanted, (label, name)
for label, stage in r['stages'].items():
    assert stage['accepted'] and stage['quiescent_release'] and stage['outer_error'] is None
    assert stage['wall_ns'] <= stage['projection_ns']
    limit = 128_000_000_000 if 'host-cuda-link' in label else 17_000_000_000
    assert stage['aggregate_CPU_ns'] <= limit and stage['group_peak_bytes'] <= 4_294_967_296
    assert not any(stage['memory_events_delta'].get(k, 0) for k in ('oom', 'oom_kill', 'oom_group_kill'))
assert all(line in whole.decode() for line in r['literal_first_control_output_lines'])
assert r['fixed_left_and_right_fixture_fibres'] == [2] and r['fixed_blind_gap_release'] == 'Released(2)'
assert r['sharedsignedresponse_matches_actual_complete_nativeWords_everycomplex_coordinate_at_everycrossing']
assert r['exact_grain_leader_union_matches_external_completionWords']
assert not r['scientific_job'] and not r['GPU_runtime'] and not r['Git_publication']
assert r['no_duplicate_test_execution_or_predecessor_credit_transfer']
assert r['broadworkspace_guard_doctest_idleGPU_gates_independently_unclaimed']

(dest / 'WHOLE_NATIVE_OUTPUT.v1.txt').write_bytes(whole)
(dest / 'SOURCE_INPUTS.v1.json').write_text(json.dumps(inputs, indent=2) + '\n')
summary = dict(
    accepted=True, source_commit=head, source_base=r['source_base'],
    original_validation_pin=pin(validation.read_bytes()),
    all_original_artifacts_rehashed=len(r['artifacts']),
    original_artifact_bytes=sum(v['bytes'] for v in r['artifacts'].values()),
    git_and_snapshot_inputs_verified=len(inputs), native_build_runtime_inputs_verified=len(native),
    original_source_snapshot_pin=pin(named('SOURCE_SNAPSHOT.v1.json')),
    original_build_seal_pin=pin(named(build + '.input_seal.json')),
    original_runtime_seal_pins=seal_pins,
    all_local_artifacts_fresh_false=True, fresh_local_targets=len(local),
    host_executable=host['executable_pin'], actual_unique_tests=names, actual_runtime_groups=18,
    whole_unfiltered_output_pin=pin(whole), fixed_left_and_right_fixture_fibres=[2], fixed_blind_gap_release='Released(2)',
    all_complex_coordinate_crossing_equalities_pass=True, exact_grain_leader_unions_pass=True,
    first_controls_native_Words=[13, 19], maximum_crossings=3,
    all_caps_cleanup_pass=True, stages=r['stages'], queue_namespace_filter_metadata_repair=repair,
    duplicate_test_execution=False, unchanged_Lean_not_recompiled=True,
    mechanical_controls_only=True, reconstruction_or_holdout_claim=False,
    scientific_job=False, GPU_runtime=False, broad_workspace_gates_unclaimed=True,
    scope='exact one-hole linear/unit completion certificate and affected native controls; no task accuracy or useful communication claim',
)
(dest / 'ACCEPTANCE_JOIN.v1.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: summary[k] for k in ('accepted', 'source_commit', 'all_original_artifacts_rehashed', 'original_artifact_bytes', 'git_and_snapshot_inputs_verified', 'fresh_local_targets', 'actual_runtime_groups', 'fixed_left_and_right_fixture_fibres', 'fixed_blind_gap_release')}, indent=2))
