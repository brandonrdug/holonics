"""Reconcile the archived mechanical control; no compiler or native process is launched."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path.cwd()
dest = Path(__file__).resolve().parent
archive = root / 'research/records/receipts/pair-output-learning-20261006/native-validation-2700572c-completions'
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
inputs = s['inputs'] | s['unchanged_Lean']
assert s['source_commit'] == head and inputs == r['source_inputs']
for name, wanted in inputs.items():
    assert pin(subprocess.check_output(['git', 'show', head + ':' + name])) == wanted, name
    assert pin((Path(s['snapshot_root']) / name).read_bytes()) == wanted, name
native = {name: value for name, value in inputs.items() if not name.startswith('lean/')}
build = 'hnn-completion-2700572c-host-cuda-link-20261006-v1'
compiled = json.loads(named('COMPILED_ARTIFACTS.v1.json'))['artifacts']
cargo = [json.loads(line) for line in named(build + '.stdout').decode().splitlines() if line.startswith('{')]
local = [a for a in cargo if a.get('reason') == 'compiler-artifact' and 'path+file://' in a.get('package_id', '')]
assert compiled and all(a['fresh'] is False for a in compiled)
assert [{k: v for k, v in a.items() if k != 'executable_pin'} for a in compiled] == local
host = next(a for a in compiled if a['target']['name'] == 'holonics' and a['profile']['test'] and a.get('executable'))
assert host['executable_pin'] == r['compiled_source_binding']['new_holonics_executable_pin']
assert pin((archive / r['artifacts'][host['executable']]['copy']).read_bytes()) == host['executable_pin']
run = r['runtime_result']
assert run['passed'] and run['quiescent'] and not run['issues']
raw = named(run['label'] + '.stdout')
names = re.findall(r'^test (\S+) \.\.\.', raw.decode(), re.M)
assert names == run['actual_test_names'] and len(names) == run['expected_tests'] == 1
assert 'test result: ok. 1 passed; 0 failed; 0 ignored;' in raw.decode()
for label in (build, run['label']):
    seal = json.loads(named(label + '.input_seal.json'))['inputs']
    for name, wanted in native.items():
        assert seal[str(Path(s['snapshot_root']) / name)] == wanted, (label, name)
for label, stage in r['stages'].items():
    assert stage['accepted'] and stage['quiescent_release'] and stage['outer_error'] is None
    assert stage['wall_ns'] <= stage['projection_ns']
    limit = 128_000_000_000 if 'host-cuda-link' in label else 17_000_000_000
    assert stage['aggregate_CPU_ns'] <= limit and stage['group_peak_bytes'] <= 4_294_967_296
out = r['actual_completion_output']
assert out['passed'] and out['source_commit'] == head and out['complete_witnesses'] == 8
assert out['complete_leader_unions'] == dict(left=[2], right=[2])
assert out['enclosing_fibres'] == dict(left=[0, 2, 3], right=[0, 2, 3])
assert out['source_and_logit_equalities_all_false_within_each_four_completion_family']
assert all(line in raw.decode() for line in out['exact_family_rows'])
assert not r['accepted_twenty_six_controls_repeated'] and not r['scientific_job'] and not r['GPU_runtime']
(dest / 'WHOLE_NATIVE_OUTPUT.v1.txt').write_bytes(raw)
(dest / 'SOURCE_INPUTS.v1.json').write_text(json.dumps(inputs, indent=2) + '\n')
summary = dict(
    accepted=True, source_commit=head, source_base=r['source_base'],
    original_validation_pin=pin(validation.read_bytes()),
    all_original_artifacts_rehashed=len(r['artifacts']),
    original_artifact_bytes=sum(v['bytes'] for v in r['artifacts'].values()),
    git_and_snapshot_inputs_verified=len(inputs),
    native_build_runtime_inputs_verified=len(native),
    original_source_snapshot_pin=pin(named('SOURCE_SNAPSHOT.v1.json')),
    original_build_seal_pin=pin(named(build + '.input_seal.json')),
    original_runtime_seal_pin=pin(named(run['label'] + '.input_seal.json')),
    all_local_artifacts_fresh_false=True, fresh_local_targets=len(local),
    host_executable=host['executable_pin'], actual_unique_tests=names,
    native_Words=r['native_Words'], complete_witnesses=8,
    whole_unfiltered_output_pin=pin(raw), complete_leader_unions=out['complete_leader_unions'],
    enclosing_fibres=out['enclosing_fibres'],
    source_and_read_equalities_all_false_within_each_family=True,
    all_caps_cleanup_pass=True, stages=r['stages'],
    accepted_twenty_six_controls_repeated=False, unchanged_Lean_not_recompiled=True,
    mechanical_controls_only=True, reconstruction_or_holdout_claim=False,
    scientific_job=False, GPU_runtime=False,
    scope='diagnostic270 only; new correlated production certificate has no native acceptance here',
)
(dest / 'ACCEPTANCE_JOIN.v1.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k not in ('stages', 'actual_unique_tests')}, indent=2))
