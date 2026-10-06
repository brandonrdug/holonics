"""Preserve completed exact-source validation evidence without Git mutation."""
import hashlib
import json
import shutil
import time
from pathlib import Path

ROOT = Path('/home/b/Workspaces/holonics')
R = Path(__file__).resolve().parent
Q = R / 'hnn-material-f9caaaba-20261006'
W = ROOT / '.local/wt/material-learning'
D = W / 'research/records/receipts/leaky-source-domain-20261006/native-validation-f9caaaba'
started = time.monotonic_ns()
assert not D.exists(), D
D.mkdir(parents=True)

def read(p):
    return json.loads(Path(p).read_text())

def pin(p):
    data = Path(p).read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

files = {}
def copy(p, relative):
    p = Path(p)
    expected = pin(p)
    target = D / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists(), target
    shutil.copy2(p, target)
    assert pin(p) == expected == pin(target)
    files[str(relative)] = {'original_path': str(p), **expected}

snapshot = read(Q / 'SOURCE_SNAPSHOT.v1.json')
request = read(snapshot['owner_request'])
controls = [read(Q / f'CONTROL_RESULT.group{n}.v1.json') for n in range(1, 9)]
assert all(c['passed'] for c in controls)
assert sum(c['expected_tests'] for c in controls) == 18
names = [name for c in controls for name in c['actual_test_names']]
assert len(names) == len(set(names)) == 18
labels = ['hnn-material-f9caaaba-cache-preparation-20261006-v1',
          'hnn-material-f9caaaba-host-cuda-link-20261006-v1']
labels += [c['label'] for c in controls]
measurements = []
for label in labels:
    assert read(R / (label + '.acceptance.json'))['passed']
    assert read(R / (label + '.release.json'))['quiescence_confirmed']
    config = read(R / (label + '.config.json'))
    final = read(R / (label + '.final.json'))
    publication = read(R / (label + '.publication.json'))
    measurements.append({'label': label, 'wall_ns': final['wall_ns'],
        'fixed_deadline_ns': config['projection_ns'],
        'measured_to_fixed_deadline': {'numerator': final['wall_ns'], 'denominator': config['projection_ns']},
        'aggregate_CPU_ns': final['final_CPU_ns'],
        'aggregate_CPU_limit_us': config['aggregate_cpu_limit_us'],
        'group_peak_bytes': int(final['unit_properties']['MemoryPeak']),
        'group_memory_max_bytes': config['group_memory_max_bytes'],
        'thread_budget': config['thread_budget'],
        'peak_child_RSS_KiB': publication['outcome'].get('peak_child_RSS_KiB'),
        'quiescent_release': True})
    for p in sorted(R.glob(label + '.*')):
        if p.is_file():
            copy(p, Path('stages') / p.name)
for relative, expected in snapshot['source_inputs'].items():
    p = Path(snapshot['source_root']) / relative
    assert pin(p) == expected
    copy(p, Path('source-v1') / relative)
for p in sorted(Q.iterdir()):
    if p.is_file() and p.suffix == '.json':
        copy(p, Path('candidate') / p.name)
for p in sorted((Q / 'preserved-local-fingerprints-v1').rglob('*')):
    if p.is_file():
        copy(p, Path('candidate/preserved-local-fingerprints-v1') / p.relative_to(Q / 'preserved-local-fingerprints-v1'))
owner_request = Path(snapshot['owner_request'])
copy(owner_request, Path('request') / owner_request.name)
for name in ['SOURCE_INPUT_MANIFEST.v6.json', 'SOURCE_MANIFEST.v6.json']:
    copy(owner_request.parent / name, Path('request') / name)
for name in ['final_stage.py', 'leased_stage_v2.py', 'bounded_stage_v1.py',
             'materialize_hnn_f9caaaba_controls_v1.py', 'grade_hnn_f9caaaba_control_v1.py',
             'preserve_hnn_f9caaaba_validation_v1.py', 'prepare_combined_test_cache_v2.py']:
    copy(R / name, Path('tools') / name)
artifacts = read(Q / 'COMPILED_ARTIFACTS.v1.json')
for d in artifacts['artifacts']:
    if d.get('executable'):
        p = Path(d['executable'])
        copy(p, Path('executables') / p.name)
for n in range(1, 9):
    copy(Q / f'CONTROL_RESULT.group{n}.v1.json', Path('controls') / f'group{n}.json')

new_read = controls[7]['measurement']
projection = {'source_commit': snapshot['source_commit'],
    'new_control_selector': request['runtime_groups'][7]['arguments'][0],
    'declared_units': 1, 'largest_completed_matching_unit_wall_ns': new_read['wall_ns'],
    'fixed_measured_followup_projection_ns': new_read['wall_ns'],
    'actual_first_development_deadline_ns': new_read['fixed_deadline_ns'],
    'first_conforming_development_read_counted_once': True,
    'followup_run_launched': False, 'no_retroactive_deadline_change': True,
    'bounded_operands': request['runtime_groups'][7]['bounded_operands']}
(D / 'NEW_CONTROL_MEASURED_PROJECTION.v1.json').write_text(json.dumps(projection, indent=2) + '\n')
files['NEW_CONTROL_MEASURED_PROJECTION.v1.json'] = pin(D / 'NEW_CONTROL_MEASURED_PROJECTION.v1.json')
result = {'passed': True, 'source_commit': snapshot['source_commit'],
    'source_base': snapshot['source_base'], 'native_controls': 18,
    'actual_unique_test_names': names, 'runtime_groups': controls,
    'measurements': measurements,
    'selected_host_CUDA_linkage_and_hnn_prediction_example': True,
    'all_local_compiler_artifacts_fresh_false': True,
    'actual_runtime_executable_differs_from_predecessor': True,
    'all_pinned_native_source_inputs_match_build_and_runtime': True,
    'unchanged_Lean_source_sha256': snapshot['source_inputs']['lean/Holonics/Foundation/ReframedRetainedMaps.lean']['sha256'],
    'unchanged_Lean_rebuilt': False,
    'prior_full17_and_final_guard2_acceptances_retained_independently': True,
    'fidelity_or_general_reconstruction_claim': False,
    'total_erasure_completion_check_is_16_source_subset_only': True,
    'native_source_sensitivity_and_exact_feature_enclosure_fixture': True,
    'full_unfiltered_runtime_output': [str(D / 'stages' / (c['label'] + '.stdout')) for c in controls],
    'scientific_job': False, 'GPU_runtime': False,
    'original_bounds_unchanged': True, 'all_stages_quiescent_and_leases_released': True,
    'preservation_wall_ns': time.monotonic_ns() - started,
    'preserved_files': files, 'no_Git_mutation': True}
(D / 'VALIDATION.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'passed': True, 'native_controls': 18, 'preserved_files': len(files),
    'validation': str(D / 'VALIDATION.json'), 'validation_pin': pin(D / 'VALIDATION.json')}))
