"""Consume the exact new research-root import without a broad library rebuild."""
from pathlib import Path
import json, shutil, re, sys
from lean_budget_v5 import pin, consumed_signature

R = Path(__file__).resolve().parent
ROOT = R.parents[2]
OLD = R / 'helical-code-20261008-v130'
L = R / 'helical-code-import-20261008-v131'
LABEL = 'helical-code-import-20261008-v131'
TARGET = 'HelicalImportConsumer'
OBJ = L / 'objects-v1'
SRC = L / 'source-v1'
SOURCE = SRC / 'HelicalImportConsumer.lean'

def read(p): return json.loads(Path(p).read_text())
def save(p, x):
    with Path(p).open('x') as f:
        json.dump(x, f, indent=2); f.write('\n')

def config(phase, inputs, outputs, argv, extra=None):
    c = read(R / 'helical-code-20261008-v130-compile.config.json')
    for key in ('mathematical_input_identity', 'expected_axiom_selectors'):
        c.pop(key, None)
    label = LABEL + '-' + phase
    core = [Path(p) for p in c['inputs'] if p.startswith(('/usr/bin/', '/home/b/.local/lib/')) or Path(p).name in ('final_stage_memory_v120.py', 'leased_stage_memory_v120.py', 'bounded_stage_memory_v120.py')]
    paths = list(dict.fromkeys([Path(__file__), *map(Path, inputs), *core]))
    c.update(label=label, scope_unit='holonics-prune-admission-' + label,
        scope='Exact newly added HolonicsResearch import line plus eight consumed accepted axiom queries; no full research library or native consumer acceptance',
        stage_kind='preparation' if phase == 'prep' else 'lean_compile',
        projection_ns=17000000000 if phase == 'prep' else 21132554884,
        group_memory_max_bytes=2**32 if phase == 'prep' else 2**33,
        minimum_MemAvailable_KiB=8388608 if phase == 'prep' else 12582912,
        inputs=list(map(str, paths)), outputs=list(map(str, outputs)), argv=argv,
        allocation_basis={'development_read': True, 'one_import_consumer': True,
                          'eight_queries_of_exact_accepted_provider': True,
                          'existing_fixed_child_ns': 17000000000,
                          'original_fixed_wrapper_ns': 21132554884,
                          'no_deadline_CPU_or_memory_increase': True})
    if extra: c.update(extra)
    c['expected_inputs'] = {str(p.resolve()): pin(p.resolve()) for p in paths}
    save(R / (label + '.config.json'), c)
    print(label)

mode = sys.argv[1]
if mode == 'prep':
    accepted = 'helical-code-20261008-v130-compile'
    assert read(R / (accepted + '.acceptance.json'))['passed']
    assert read(R / (accepted + '.release.json'))['quiescence_confirmed']
    assert read(OLD / 'KERNEL_VALIDATION.json')['kernel_accepted']
    L.mkdir(); SRC.mkdir()
    shutil.copytree(OLD / 'objects-v1', OBJ)
    selectors = ['phaseTransport_pairing', 'face_complementReverse', 'strandFace_repeatWord_of_fixed',
                 'dihedralFrame_bijective', 'card_free_involutions_fin4', 'slipped_contacts_eq',
                 'duplex_passage_linking', "geom_smul_sum_succ'"]
    selectors = ['Holonics.Transport.HelicalCode.' + s for s in selectors]
    line = 'import Holonics.Transport.HelicalCode\n'
    root = OLD / 'submitted/lean/HolonicsResearch.lean'
    assert root.read_text().splitlines()[296] + '\n' == line
    with SOURCE.open('x') as f:
        f.write(line + '\n' + ''.join('#print axioms ' + s + '\n' for s in selectors))
    scope = {'source_commit': read(OLD / 'SOURCE_ADMISSION.json')['commit'], 'root_import': str(root),
             'root_pin': pin(root), 'actual_added_line_number': 297, 'actual_added_import': line.strip(),
             'consumer_source': str(SOURCE), 'consumer_pin': pin(SOURCE), 'expected_selectors': selectors,
             'full_HolonicsResearch_root_compiled': False, 'Framework_default_target_changed': False,
             'native_helical_consumer_implemented_or_accepted': False,
             'accepted_provider_kernel': str(OLD / 'KERNEL_VALIDATION.json')}
    save(L / 'CONSUMER_SCOPE.json', scope)
    ns = read(OLD / 'PROVIDER_NAMESPACE.json')
    for row in ns['copies']:
        for part in row['parts'].values():
            origin = Path(part['copy']); dest = OBJ / origin.relative_to(OLD / 'objects-v1')
            assert pin(dest) == part['pin']; part['original'] = str(origin); part['copy'] = str(dest)
    source = OLD / 'source-v1/Holonics/Transport/HelicalCode.lean'
    obj = OBJ / 'Holonics/Transport/HelicalCode.olean'
    assert obj.exists()
    ns['copies'].append({'module': 'Holonics.Transport.HelicalCode', 'source_copy': str(source), 'source_pin': pin(source),
        'parts': {'main': {'copy': str(obj), 'original': str(OLD / 'objects-v1/Holonics/Transport/HelicalCode.olean'), 'pin': pin(obj)}},
        'provenance': {'kernel': str(OLD / 'KERNEL_VALIDATION.json'), 'acceptance': str(R / (accepted + '.acceptance.json')), 'release': str(R / (accepted + '.release.json'))}})
    namespace = L / 'PROVIDER_NAMESPACE.json'; save(namespace, ns)
    d = read(OLD / 'PREPARATION_REQUEST.json')
    d.update(target=TARGET, source=str(SOURCE), source_sha256=pin(SOURCE)['sha256'],
             object_roots=[str(OBJ), *d['object_roots'][1:]],
             source_roots=[str(SRC), str(OLD / 'source-v1'), *d['source_roots'][1:]],
             provider_namespace=str(namespace), seal_output=str(L / 'current-imports.json'),
             preparation_receipt=str(L / 'import-preparation.json'))
    d['completed_metadata_graphs'].append(str(OLD / 'current-imports.json'))
    inputs = [SOURCE, root, L / 'CONSUMER_SCOPE.json', namespace, OLD / 'SOURCE_ADMISSION.json', OLD / 'KERNEL_VALIDATION.json',
              R / (accepted + '.acceptance.json'), R / (accepted + '.release.json'), Path(d['accepted_foreign_graph']),
              *map(Path, d['completed_metadata_graphs']), Path(d['sealer']), R / 'prepare_ns_namespace_v1.py', R / 'check_namespace_lookup_v1.py']
    d['code_inputs'] = list(map(str, inputs))
    dp = L / 'PREPARATION_REQUEST.json'; save(dp, d)
    config('prep', [dp, *inputs], [d['seal_output'], d['preparation_receipt']],
           ['/usr/bin/python3.14', '-B', str(R / 'prepare_ns_namespace_v1.py'), str(dp)])
elif mode == 'compile':
    pl = LABEL + '-prep'
    assert read(R / (pl + '.acceptance.json'))['passed']
    assert read(R / (pl + '.release.json'))['quiescence_confirmed']
    d = read(L / 'PREPARATION_REQUEST.json')
    selectors = read(L / 'CONSUMER_SCOPE.json')['expected_selectors']
    obj = OBJ / 'HelicalImportConsumer.olean'
    assert not obj.exists()
    c = {'target': TARGET, 'source': str(SOURCE), 'sealer': d['sealer'], 'metadata_verifier': str(R / 'verify_lean_metadata_v1.py'),
         'import_seal': str(L / 'current-imports.json'), 'expected_selectors': selectors,
         'compiler_stdout': str(L / 'compiler.stdout'), 'compiler_stderr': str(L / 'compiler.stderr'), 'kernel_receipt': str(L / 'KERNEL_VALIDATION.json'),
         'compiler_argv': ['/usr/bin/timeout', '--signal=TERM', '--kill-after=1s', '17s', '/usr/bin/env', '-i',
                           'PATH=/usr/bin', 'HOME=/home/b', 'LANG=C', 'LC_ALL=C', 'LEAN_PATH=' + ':'.join(d['object_roots']),
                           '/home/b/.local/lib/lean-4.33.0/bin/lean', '-j1', '-M8192', '-R', str(SRC), '-o', str(obj), '-i', str(obj.with_suffix('.ilean')), str(SOURCE)]}
    dp = L / 'COMPILER_REQUEST.json'; save(dp, c)
    inputs = [dp, SOURCE, L / 'CONSUMER_SCOPE.json', L / 'current-imports.json', L / 'import-preparation.json',
              R / (pl + '.acceptance.json'), R / (pl + '.release.json'), R / (pl + '.output_seal.json'),
              R / 'check_lean_owner_v5.py', R / 'verify_lean_metadata_v1.py', Path(d['sealer'])]
    identity = {'target': TARGET, 'source_sha256': pin(SOURCE)['sha256'],
                'consumed_imports_sha256': consumed_signature(read(L / 'current-imports.json'))}
    config('compile', inputs, [obj, obj.with_suffix('.ilean'), c['compiler_stdout'], c['compiler_stderr'], c['kernel_receipt']],
           ['/usr/bin/python3.14', '-B', str(R / 'check_lean_owner_v5.py'), str(dp)],
           {'mathematical_input_identity': identity, 'expected_axiom_selectors': selectors})
else:
    raise AssertionError(mode)
