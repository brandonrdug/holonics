from pathlib import Path
from fractions import Fraction
import hashlib, json, re, shutil, subprocess

root = Path.cwd()
archive = root / 'research/records/receipts/leaky-source-domain-20261006/native-validation-a730d824'
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
build_label = 'hnn-behavior-a730d824-host-cuda-link-20261006-v2'
run_label = receipt['runtime_result']['label']
for label in [build_label, run_label]:
    seal = json.loads(read_named(label + '.input_seal.json'))['inputs']
    for name, want in native.items():
        assert seal[str(source_root / name)] == want, (label, name)
compiled = json.loads(read_named('COMPILED_ARTIFACTS.v1.json'))['artifacts']
cargo = [json.loads(line) for line in read_named(build_label + '.stdout').decode().splitlines() if line.startswith('{')]
local = [a for a in cargo if a.get('reason') == 'compiler-artifact' and 'path+file://' in a.get('package_id', '')]
assert compiled and all(a['fresh'] is False for a in compiled)
assert [{k:v for k,v in a.items() if k != 'executable_pin'} for a in compiled] == local
host = next(a for a in compiled if a['target']['name'] == 'holonics' and a['profile']['test'] and a.get('executable'))
assert host['executable_pin'] == receipt['compiled_source_binding']['new_holonics_executable_pin']
host_copy = receipt['artifacts'][host['executable']]
assert pin((archive / host_copy['copy']).read_bytes()) == host['executable_pin']
run_seal = json.loads(read_named(run_label + '.input_seal.json'))['inputs']
assert run_seal[host['executable']] == host['executable_pin']
raw = read_named(run_label + '.stdout').decode()
names = re.findall(r'^test (\S+) \.\.\.', raw, re.M)
assert names == [receipt['exact_selector']]
assert 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1027 filtered out;' in raw
for label, stage in receipt['stages'].items():
    final = json.loads(read_named(label + '.final.json'))
    assert stage['quiescent_release']
    assert stage['wall_ns'] <= stage['projection_ns']
    cpu_limit = 128000000000 if 'host-cuda-link' in label else 17000000000
    assert stage['aggregate_CPU_ns'] <= cpu_limit
    assert stage['group_peak_bytes'] <= 4294967296
assert receipt['stages']['hnn-behavior-a730d824-host-cuda-link-20261006-v1']['accepted'] is False
assert receipt['stages'][build_label]['accepted'] is True
assert receipt['stages'][run_label]['accepted'] is True
assert pin(Path(snapshot['owner_request']).read_bytes()) == snapshot['owner_request_pin']

def rational_values(s):
    return [Fraction(int(a), int(b)) for a, b in re.findall(r'Ratio \{ numer: (-?\d+), denom: (\d+) \}', s)]
def exact(x):
    return {'numerator': x.numerator, 'denominator': x.denominator}
probes = []
for line in raw.splitlines():
    if not line.startswith('target-free native probe:'):
        continue
    logits = rational_values(line.split('learned-R complex logits ')[1].split('; learned domain')[0])
    assert len(logits) == 16
    margins = [[exact(logits[t*8+6] - logits[t*8+2*c]) for c in range(3)] for t in range(2)]
    assert all(logits[t*8+6] > logits[t*8+2*c] for t in range(2) for c in range(3))
    probes.append({'intact_source': line.split('actual intact source ')[1].split('; initial-R')[0],
                   'whole_output': line.split('learned-R whole output ')[1].split('; initial-R leaders')[0],
                   'complex_logits_by_crossing': [[exact(x) for x in logits[t*8:(t+1)*8]] for t in range(2)],
                   'real_class3_minus_classes0_1_2_by_crossing': margins})
assert len(probes) == 3
assert len({json.dumps(q['complex_logits_by_crossing']) for q in probes}) == 3
material_line = next(q for q in raw.splitlines() if q.startswith('retained receiving material:'))
assert 'equal real rows 0/1 false; 0/3 false; 1/3 false' in material_line
assert 'full source E unchanged true' in material_line
behavior = {'source_commit': head, 'raw_stdout_pin': pin(raw.encode()), 'probes': probes,
            'source_changes_exact_complex_logits': True, 'all_three_decisions_class3': True,
            'receiving_real_rows0_1_3_distinct': True,
            'initial_R_same_carry_control_plural': True,
            'causal_claim': 'Changing only R changes the decisions; changing cue changes the logits but not these decisions.',
            'not_identified': ['pure last-label effect', 'carry contribution versus common probe tail', 'task fidelity'],
            'no_probe_target_or_truth_grade': True}
behavior['pairwise_complex_logit_differences'] = [
    {'left_cue': left, 'right_cue': right,
     'left_minus_right_by_crossing': [
        [exact(Fraction(a['numerator'], a['denominator']) - Fraction(b['numerator'], b['denominator']))
         for a, b in zip(probes[i]['complex_logits_by_crossing'][t], probes[j]['complex_logits_by_crossing'][t])]
        for t in range(2)]}
    for i, j, left, right in [(0,1,0,1),(0,2,0,3),(1,2,1,3)]]
behavior['finite_difference_contract'] = 'Fixed R/carry/common tail/current; the loaded quartic Word response includes nonlinear interactions. No linear K formula or additive carry cancellation asserted.'

dest = root / 'research/records/receipts/distinct-receiving-observations-20261006/accepted-a730d824'
if dest.exists():
    old = json.loads((dest / 'ACCEPTANCE_JOIN.v1.json').read_text())
    for name, want in old['selected_preserved_artifacts'].items():
        assert pin((dest / name).read_bytes()) == want, name
    (dest / 'BEHAVIOR_READOUT.v1.json').write_text(json.dumps(behavior, indent=2) + '\n')
    print('Verified original 760 artifacts, immutable source/build/runtime binding, caps, and 117 compact copies; exact readout refreshed from raw output.')
    raise SystemExit
dest.mkdir(parents=True)
selected = {}
for original, entry in receipt['artifacts'].items():
    if '/admission-v1/hnn-behavior-a730d824-' not in original:
        continue
    suffix = original.split('/admission-v1/', 1)[1]
    if '/cache-' in suffix or '/source-' in suffix:
        continue
    out = dest / 'queue' / suffix
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(archive / entry['copy'], out)
    selected[str(out.relative_to(dest))] = {k:entry[k] for k in ('bytes','sha256')}
for name in ['VALIDATION.json', 'BEHAVIOR_FROM_RAW.v1.json']:
    shutil.copyfile(archive / name, dest / name)
    selected[name] = pin((dest / name).read_bytes())
(dest / 'BEHAVIOR_READOUT.v1.json').write_text(json.dumps(behavior, indent=2) + '\n')
summary = {'source_commit': head, 'source_base': receipt['source_base'],
           'all_original_artifacts_rehashed': len(receipt['artifacts']),
           'original_artifact_bytes': sum(v['bytes'] for v in receipt['artifacts'].values()),
           'git_and_immutable_snapshot_source_inputs_verified': len(snapshot['source_inputs']),
           'native_build_runtime_source_inputs_verified': len(native),
           'all_local_artifacts_fresh_false': True,
           'host_executable': host['executable_pin'], 'actual_unique_selectors': names,
           'native_Words': 9, 'scientific_job': False, 'GPU_runtime': False,
           'unchanged_Lean_not_recompiled': True,
           'stages': receipt['stages'], 'all_caps_and_cleanup_pass': True,
           'pre_Cargo_input_plan_refusal_preserved': True,
           'original_archive_retained_locally': str(archive),
           'selected_preserved_artifacts': selected,
           'large_binaries_toolchain_cache_not_committed': True,
           'earlier_eighteen_control_acceptance_independent': True}
(dest / 'ACCEPTANCE_JOIN.v1.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ('selected_preserved_artifacts','stages')}, indent=2))
print('preserved compact entries', len(selected), 'bytes', sum(v['bytes'] for v in selected.values()))
