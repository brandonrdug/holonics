from pathlib import Path
import hashlib, json, re, shutil, subprocess

root = Path.cwd()
archive = root / 'research/records/receipts/station-pair-source-20261006/native-validation-518e1e3f'
dest = Path(__file__).resolve().parent
receipt = json.loads((archive / 'VALIDATION.json').read_text())
head = receipt['source_commit']

def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def read_named(name):
    hits = [v for k, v in receipt['artifacts'].items() if k.endswith('/' + name)]
    assert len(hits) == 1, name
    return (archive / hits[0]['copy']).read_bytes()

for name, want in receipt['artifacts'].items():
    assert pin((archive / want['copy']).read_bytes()) == {k: want[k] for k in ('bytes', 'sha256')}, name
snapshot = json.loads(read_named('SOURCE_SNAPSHOT.v1.json'))
source_root = Path(snapshot['source_root'])
assert snapshot['source_commit'] == head
assert snapshot['source_inputs'] == receipt['source_inputs']
for name, want in snapshot['source_inputs'].items():
    assert pin(subprocess.check_output(['git', 'show', head + ':' + name])) == want, name
    assert pin((source_root / name).read_bytes()) == want, name
native = {n: v for n, v in snapshot['source_inputs'].items() if not n.startswith('lean/')}
build_label = 'hnn-intact-pair-518e1e3f-host-cuda-link-20261006-v1'
compiled = json.loads(read_named('COMPILED_ARTIFACTS.v1.json'))['artifacts']
cargo = [json.loads(line) for line in read_named(build_label + '.stdout').decode().splitlines() if line.startswith('{')]
local = [a for a in cargo if a.get('reason') == 'compiler-artifact' and 'path+file://' in a.get('package_id', '')]
assert compiled and all(a['fresh'] is False for a in compiled)
assert [{k:v for k,v in a.items() if k != 'executable_pin'} for a in compiled] == local
host = next(a for a in compiled if a['target']['name'] == 'holonics' and a['profile']['test'] and a.get('executable'))
assert host['executable_pin'] == receipt['compiled_source_binding']['new_holonics_executable_pin']
assert pin((archive / receipt['artifacts'][host['executable']]['copy']).read_bytes()) == host['executable_pin']
actual_names = []
raw_outputs = {}
for run in receipt['runtime_results']:
    label = run['label']
    assert run['passed'] and run['quiescent'] and not run['issues']
    raw = read_named(label + '.stdout').decode()
    names = re.findall(r'^test (\S+) \.\.\.', raw, re.M)
    assert names == run['actual_test_names'], label
    assert len(names) == run['expected_tests'], label
    assert re.search(r'test result: ok\. ' + str(len(names)) + r' passed; 0 failed; 0 ignored;', raw), label
    actual_names.extend(names)
    raw_outputs[label] = raw
    seal = json.loads(read_named(label + '.input_seal.json'))['inputs']
    for name, want in native.items():
        assert seal[str(source_root / name)] == want, (label, name)
assert len(actual_names) == len(set(actual_names)) == 24
assert sorted(actual_names) == sorted(receipt['actual_test_names'])
build_seal = json.loads(read_named(build_label + '.input_seal.json'))['inputs']
for name, want in native.items():
    assert build_seal[str(source_root / name)] == want, name
for label, stage in receipt['stages'].items():
    assert stage['accepted'] and stage['quiescent_release'] and stage['outer_error'] is None
    assert stage['wall_ns'] <= stage['projection_ns']
    assert stage['aggregate_CPU_ns'] <= (128000000000 if 'host-cuda-link' in label else 17000000000)
    assert stage['group_peak_bytes'] <= 4294967296
assert pin(Path(snapshot['owner_request']).read_bytes()) == snapshot['owner_request_pin']

controls = []
for raw in raw_outputs.values():
    for line in raw.splitlines():
        if 'matched retained-reader control ' in line:
            prefix = line.split('matched retained-reader control ', 1)[1]
            controls.append({'label': prefix.split(':', 1)[0],
                             'whole_output_and_leaders': prefix.split('; whole cells ', 1)[1].split('; complex logits ', 1)[0],
                             'raw_line': line})
assert len(controls) == 9
readout = {'source_commit': head, 'matched_controls': controls,
           'claim': 'Matched receiving-material stages change the gap decisions. Carry controls include clock/phase; absent-source changes the population chart.',
           'not_identified': ['pure last-label recency', 'cue versus common-tail nonlinear attribution', 'task fidelity', 'untouched holdout accuracy'],
           'synthetic_mechanical_controls_only': True}
selected = {}
for original, entry in receipt['artifacts'].items():
    if '/admission-v1/hnn-intact-pair-518e1e3f-' not in original:
        continue
    suffix = original.split('/admission-v1/', 1)[1]
    if any(token in suffix for token in ('/cache-', '/source-', '/target/', '/external/')):
        continue
    out = dest / 'queue' / suffix
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(archive / entry['copy'], out)
    selected[str(out.relative_to(dest))] = {k:entry[k] for k in ('bytes','sha256')}
shutil.copyfile(archive / 'VALIDATION.json', dest / 'VALIDATION.json')
selected['VALIDATION.json'] = pin((dest / 'VALIDATION.json').read_bytes())
(dest / 'BEHAVIOR_READOUT.v1.json').write_text(json.dumps(readout, indent=2) + '\n')
summary = {'source_commit': head, 'source_base': receipt['source_base'],
           'all_original_artifacts_rehashed': len(receipt['artifacts']),
           'original_artifact_bytes': sum(v['bytes'] for v in receipt['artifacts'].values()),
           'git_and_immutable_snapshot_source_inputs_verified': len(snapshot['source_inputs']),
           'native_build_runtime_source_inputs_verified': len(native),
           'all_local_artifacts_fresh_false': True, 'fresh_local_targets': len(local),
           'host_executable': host['executable_pin'], 'actual_unique_selectors': actual_names,
           'runtime_groups': len(receipt['runtime_results']), 'new_control_Words': 48,
           'scientific_job': False, 'GPU_runtime': False, 'unchanged_Lean_not_recompiled': True,
           'stages': receipt['stages'], 'all_caps_and_cleanup_pass': True,
           'selected_preserved_artifacts': selected, 'large_binaries_toolchain_cache_not_committed': True,
           'mechanical_controls_only': True, 'useful_reconstruction_established': False}
(dest / 'ACCEPTANCE_JOIN.v1.json').write_text(json.dumps(summary, indent=2) + '\n')
print('Verified', len(receipt['artifacts']), 'original artifacts and', len(native), 'native source bindings; 24 unique controls passed.')
print('Preserved', len(selected), 'compact artifacts,', sum(v['bytes'] for v in selected.values()), 'bytes.')
for control in controls:
    print(control['label'] + ': ' + control['whole_output_and_leaders'])
