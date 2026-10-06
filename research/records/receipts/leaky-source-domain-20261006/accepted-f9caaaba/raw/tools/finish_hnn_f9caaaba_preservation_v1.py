"""Finish metadata after the receipt writer's wrong Lean-key lookup; no job rerun."""
import hashlib
import json
import shutil
from pathlib import Path

ROOT = Path('/home/b/Workspaces/holonics')
R = Path(__file__).resolve().parent
D = ROOT / '.local/wt/material-learning/research/records/receipts/leaky-source-domain-20261006/native-validation-f9caaaba'
Q = R / 'hnn-material-f9caaaba-20261006'

def read(p):
    return json.loads(Path(p).read_text())

def pin(p):
    data = Path(p).read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

snapshot = read(D / 'candidate/SOURCE_SNAPSHOT.v1.json')
controls = [read(D / f'controls/group{n}.json') for n in range(1, 9)]
assert all(c['passed'] for c in controls)
names = [name for c in controls for name in c['actual_test_names']]
assert len(names) == len(set(names)) == 18
for relative, expected in snapshot['source_inputs'].items():
    assert pin(D / 'source-v1' / relative) == expected == pin(Path(snapshot['source_root']) / relative)
lean = [(k, v) for k, v in snapshot['source_inputs'].items() if k.endswith('.lean')]
assert len(lean) == 1
assert lean[0][0] == 'lean/Holonics/HNN/ReframedMoment.lean'
assert lean[0][1]['sha256'] == '4ffc65a60f4e72c8bc63c637d7e6480ada2e8721a002e53c487635e64cd93f2e'
assert not (D / 'VALIDATION.json').exists()
failure = {'kind': 'receipt_metadata_only', 'native_and_Lean_job_rerun': False,
    'prior_writer': 'tools/preserve_hnn_f9caaaba_validation_v1.py',
    'error': "KeyError: 'lean/Holonics/Foundation/ReframedRetainedMaps.lean'",
    'actual_pinned_unchanged_Lean_owner': lean[0][0],
    'all_copied_evidence_retained': True,
    'effect_on_completed_build_or_control_acceptance': False}
(D / 'PRESERVATION_METADATA_CORRECTION.v1.json').write_text(json.dumps(failure, indent=2) + '\n')
shutil.copy2(__file__, D / 'tools' / Path(__file__).name)
labels = ['hnn-material-f9caaaba-cache-preparation-20261006-v1',
          'hnn-material-f9caaaba-host-cuda-link-20261006-v1'] + [c['label'] for c in controls]
measurements = []
for label in labels:
    prefix = D / 'stages'
    assert read(prefix / (label + '.acceptance.json'))['passed']
    assert read(prefix / (label + '.release.json'))['quiescence_confirmed']
    config = read(prefix / (label + '.config.json'))
    final = read(prefix / (label + '.final.json'))
    publication = read(prefix / (label + '.publication.json'))
    for p in R.glob(label + '.*'):
        if p.is_file():
            assert pin(p) == pin(prefix / p.name)
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
artifacts = read(D / 'candidate/COMPILED_ARTIFACTS.v1.json')
for d in artifacts['artifacts']:
    assert d['fresh'] is False
    if d.get('executable'):
        assert pin(d['executable']) == d['executable_pin'] == pin(D / 'executables' / Path(d['executable']).name)
files = {str(p.relative_to(D)): pin(p) for p in sorted(D.rglob('*')) if p.is_file()}
result = {'passed': True, 'source_commit': snapshot['source_commit'],
    'source_base': snapshot['source_base'], 'native_controls': 18,
    'actual_unique_test_names': names, 'runtime_groups': controls,
    'measurements': measurements,
    'selected_host_CUDA_linkage_and_hnn_prediction_example': True,
    'all_local_compiler_artifacts_fresh_false': True,
    'actual_runtime_executable_differs_from_predecessor': True,
    'all_pinned_native_source_inputs_match_build_and_runtime': True,
    'unchanged_Lean_owner': lean[0][0], 'unchanged_Lean_source_sha256': lean[0][1]['sha256'],
    'unchanged_Lean_rebuilt': False,
    'prior_full17_and_final_guard2_acceptances_retained_independently': True,
    'fidelity_or_general_reconstruction_claim': False,
    'total_erasure_completion_check_is_16_source_subset_only': True,
    'native_source_sensitivity_and_exact_feature_enclosure_fixture': True,
    'full_unfiltered_runtime_output': [str(D / 'stages' / (c['label'] + '.stdout')) for c in controls],
    'scientific_job': False, 'GPU_runtime': False,
    'original_bounds_unchanged': True, 'all_stages_quiescent_and_leases_released': True,
    'receipt_metadata_correction_preserved': True,
    'preserved_files': files, 'no_Git_mutation': True}
(D / 'VALIDATION.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'passed': True, 'native_controls': 18, 'preserved_files': len(files),
    'validation': str(D / 'VALIDATION.json'), 'validation_pin': pin(D / 'VALIDATION.json')}))
