"""Exact frozen helical source; existing sole queue, no maintained-source edits."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, sys
from lean_budget_v5 import pin, consumed_signature, prior_failed_identities

R = Path(__file__).resolve().parent
ROOT = R.parents[2]
L = R / 'helical-code-20261008-v129'
WT = ROOT / '.local/wt/helical-code'
COMMIT = '12fcee78736a4e947adfbc0e76cb5bec2b9b4a68'
TARGET = 'Holonics.Transport.HelicalCode'
LABEL = 'helical-code-20261008-v129'
LS = R / 'integration-bd29-20261008/lean-source-v1/lean'
BASEOBJ = R / 'integration-default-combined-20261008-v119/objects-v1'
AUDIT = R / 'integration-default-capacity-cache-audit-20261008-v119/RESULT.json'
TEMPLATE = R / 'integration-default-combined-06-20261008-v120-compile.config.json'
PREP_TEMPLATE = R / 'integration-default-combined-20261008-v119/consumer01/PREPARATION_REQUEST.json'

def read(p):
    return json.loads(Path(p).read_text())

def save(p, value):
    with Path(p).open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')

def blob(rel, commit=COMMIT):
    return subprocess.check_output(['git', '-C', str(WT), 'show', commit + ':' + rel])

def code_without_comments(text):
    out = []
    depth = i = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i]); i += 1
    assert depth == 0
    return ''.join(out).split()

def config(phase, inputs, outputs, argv, extra=None):
    c = read(TEMPLATE)
    for key in ('mathematical_input_identity', 'expected_axiom_selectors', 'allocation_basis'):
        c.pop(key, None)
    label = LABEL + '-' + phase
    core = [Path(p) for p in c['inputs'] if p.startswith(('/usr/bin/', '/home/b/.local/lib/'))]
    core += [R / (n + '.py') for n in ('final_stage_memory_v120', 'leased_stage_memory_v120', 'bounded_stage_memory_v120')]
    paths = list(dict.fromkeys([Path(__file__), *map(Path, inputs), *core]))
    c.update(label=label, scope_unit='holonics-prune-admission-' + label,
             stage_kind='preparation' if phase == 'prep' else 'lean_compile',
             scope='Exact frozen helical module and 81 standard-axiom queries; independent source review and native consumer excluded',
             source_commit=COMMIT, projection_ns=17000000000 if phase == 'prep' else 21132554884,
             group_memory_max_bytes=2**32 if phase == 'prep' else 2**33,
             minimum_MemAvailable_KiB=8388608 if phase == 'prep' else 12582912,
             explicit_user_8GiB_authorization=True, address_space_max_bytes=-1,
             aggregate_cpu_limit_us=17000000, aggregate_cpu_stop_margin_us=1000000,
             thread_budget=1, inputs=list(map(str, paths)), outputs=list(map(str, outputs)), argv=argv,
             allocation_basis={'development_read': True, 'declared_compile_units': 1,
                 'largest_prior_accepted_complete_compiler_wall_ns': 15278561897,
                 'existing_fixed_child_window_ns': 17000000000,
                 'largest_prior_full_import_preparation_wall_ns': 12779337307,
                 'existing_complete_wrapper_ceiling_ns': 21132554884,
                 'new_elaboration_unmeasured': True,
                 'no_unchanged_failed_retry': True,
                 'no_deadline_or_CPU_cap_increase': True,
                 'memory_ceiling_authorized_by_parent': 2**33})
    if extra:
        c.update(extra)
    c['expected_inputs'] = {str(p.resolve()): pin(p.resolve()) for p in paths}
    save(R / (label + '.config.json'), c)
    print(label)

mode = sys.argv[1]
OBJ = L / 'objects-v1'
SRC = L / 'source-v1'
source = SRC / 'Holonics/Transport/HelicalCode.lean'
if mode == 'prep':
    L.mkdir(); OBJ.mkdir(); SRC.mkdir()
    msg = ROOT / '.local/agent-mailbox/messages/d96836b645354bb4ab21178995d9249d.json'
    handoff = read(msg)
    selectors = re.findall(r'Holonics\.Transport\.HelicalCode\.\S+', handoff['body'].split('Axiom selectors:')[1])
    assert len(selectors) == len(set(selectors)) == 81
    expected = {
        'lean/Holonics/Transport/HelicalCode.lean': '9077b60c6e0c4cede258e61d5c081a6ce8f881e495105633199979d491f590fa',
        'lean/HolonicsResearch.lean': '472ebcea28d5141f930653c0bb1f679e74c06d60d69adbc7d8a6af8153eac522',
        'lean/HolonicsResearch/Foundation/TopologicalReceiver.lean': '318b2133282883518ca30d7614f48a28770ea9aa42e22e5836860624dc28677c'}
    pins = {}
    for rel, sha in expected.items():
        data = blob(rel)
        assert hashlib.sha256(data).hexdigest() == sha
        dest = L / 'submitted' / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        with dest.open('xb') as f: f.write(data)
        pins[rel] = pin(dest)
    body = (L / 'submitted/lean/Holonics/Transport/HelicalCode.lean').read_text()
    assert len(body.splitlines()) == 989
    assert not re.search(r'(?m)^\s*(axiom|sorry)\b', body)
    assert not re.search(r'\b(sorry|native_decide)\b', ' '.join(code_without_comments(body)))
    declared = re.findall(r'(?m)^(?:@\[[^\]]+\]\s+)?(?:def|theorem)\s+(\S+)', body)
    assert set('Holonics.Transport.HelicalCode.' + n for n in declared) == set(selectors)
    source.parent.mkdir(parents=True)
    with source.open('x') as f:
        f.write(body + '\n' + ''.join('#print axioms ' + n + '\n' for n in selectors))
    parent = subprocess.check_output(['git', '-C', str(WT), 'rev-parse', COMMIT + '^'], text=True).strip()
    old_root = blob('lean/HolonicsResearch.lean', parent).decode()
    new_root = blob('lean/HolonicsResearch.lean').decode()
    assert new_root == old_root.replace('import Holonics.Transport.HelicalPairInteraction\n', 'import Holonics.Transport.HelicalPairInteraction\nimport Holonics.Transport.HelicalCode\n')
    assert code_without_comments(blob('lean/HolonicsResearch/Foundation/TopologicalReceiver.lean').decode()) == code_without_comments(blob('lean/HolonicsResearch/Foundation/TopologicalReceiver.lean', parent).decode())
    audit = read(AUDIT)
    pending = ['Holonics.Transport.HelicalPairInteraction']; seen = set()
    while pending:
        name = pending.pop()
        if name in seen: continue
        seen.add(name)
        if name in audit['modules']: pending.extend(audit['modules'][name]['imports'])
    copies = []
    for name in sorted(n for n in seen if n.startswith('Holonics.')):
        row = audit['modules'][name]
        assert row['source_trace_match'] and row['artifact']['all_expected_parts_match_trace']
        rel = 'lean/' + name.replace('.', '/') + '.lean'
        assert hashlib.sha256(blob(rel)).hexdigest() == row['source_metadata']['sha256']
        assert pin(Path(row['source']))['sha256'] == row['source_metadata']['sha256']
        parts = {}
        for key, value in row['artifact']['parts'].items():
            meta = value['metadata']
            if not meta['present']: continue
            origin = BASEOBJ / Path(*name.split('.')).parent / Path(meta['path']).name
            pn = {'sha256': meta['sha256'], 'bytes': meta['target_stat']['bytes']}
            assert pin(origin) == pn
            dest = OBJ / Path(*name.split('.')).parent / origin.name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(origin, dest)
            assert pin(dest) == pn
            parts[key] = {'copy': str(dest), 'original': str(origin), 'pin': pn}
        copies.append({'module': name, 'source_copy': row['source'], 'source_pin': pin(Path(row['source'])), 'parts': parts,
                       'provenance': {'source_and_all_artifact_trace_parts_match': True, 'audit': str(AUDIT)}})
    ns = L / 'PROVIDER_NAMESPACE.json'
    save(ns, {'copies': copies, 'source_commit': COMMIT})
    admission = {'commit': COMMIT, 'tree': subprocess.check_output(['git', '-C', str(WT), 'rev-parse', COMMIT + '^{tree}'], text=True).strip(),
                 'submitted_pins': pins, 'source_body_pin': pins['lean/Holonics/Transport/HelicalCode.lean'],
                 'compiler_source_pin': pin(source), 'only_added_queries': True, 'selectors': selectors,
                 'custom_import_closure_count': len(copies), 'retained_provider_sources_match_commit': True,
                 'research_root_only_added_import': True, 'topology_only_comments_changed': True,
                 'Framework_default_target_unchanged': True, 'handoff': str(msg), 'native_consumer_grade': 'design only',
                 'full_research_library_check': False, 'compiler_launched': False}
    save(L / 'SOURCE_ADMISSION.json', admission)
    d = read(PREP_TEMPLATE)
    d.update(target=TARGET, source=str(source), source_sha256=pin(source)['sha256'],
             object_roots=[str(OBJ), *d['object_roots'][1:]],
             source_roots=[str(SRC), str(LS), *d['source_roots'][2:]], provider_namespace=str(ns),
             seal_output=str(L / 'current-imports.json'), preparation_receipt=str(L / 'import-preparation.json'))
    inputs = [source, ns, L / 'SOURCE_ADMISSION.json', msg, AUDIT, Path(d['accepted_foreign_graph']),
              *map(Path, d['completed_metadata_graphs']), Path(d['sealer']), R / 'prepare_ns_namespace_v1.py', R / 'check_namespace_lookup_v1.py',
              *[L / 'submitted' / p for p in expected]]
    d['code_inputs'] = list(map(str, inputs))
    dp = L / 'PREPARATION_REQUEST.json'; save(dp, d)
    config('prep', [*inputs, dp], [d['seal_output'], d['preparation_receipt']],
           ['/usr/bin/python3.14', '-B', str(R / 'prepare_ns_namespace_v1.py'), str(dp)])
elif mode == 'compile':
    pl = LABEL + '-prep'
    assert read(R / (pl + '.acceptance.json'))['passed']
    assert read(R / (pl + '.release.json'))['quiescence_confirmed']
    d = read(L / 'PREPARATION_REQUEST.json')
    selectors = read(L / 'SOURCE_ADMISSION.json')['selectors']
    graph = read(L / 'current-imports.json')
    ident = {'target': TARGET, 'source_sha256': pin(source)['sha256'], 'consumed_imports_sha256': consumed_signature(graph)}
    failed, history = prior_failed_identities(R, TARGET, ident['source_sha256'])
    assert ident not in failed
    obj = OBJ / 'Holonics/Transport/HelicalCode.olean'; obj.parent.mkdir(parents=True, exist_ok=True)
    assert not obj.exists()
    desc = {'target': TARGET, 'source': str(source), 'sealer': d['sealer'], 'metadata_verifier': str(R / 'verify_lean_metadata_v1.py'),
            'import_seal': str(L / 'current-imports.json'), 'expected_selectors': selectors,
            'compiler_stdout': str(L / 'compiler.stdout'), 'compiler_stderr': str(L / 'compiler.stderr'), 'kernel_receipt': str(L / 'KERNEL_VALIDATION.json'),
            'compiler_argv': ['/usr/bin/timeout', '--signal=TERM', '--kill-after=1s', '17s', '/usr/bin/env', '-i',
                              'PATH=/usr/bin', 'HOME=/home/b', 'LANG=C', 'LC_ALL=C', 'LEAN_PATH=' + ':'.join(d['object_roots']),
                              '/home/b/.local/lib/lean-4.33.0/bin/lean', '-j1', '-M8192', '-R', str(SRC), '-o', str(obj), '-i', str(obj.with_suffix('.ilean')), str(source)]}
    dp = L / 'COMPILER_REQUEST.json'; save(dp, desc)
    inputs = [dp, source, L / 'SOURCE_ADMISSION.json', L / 'current-imports.json', L / 'import-preparation.json',
              R / (pl + '.acceptance.json'), R / (pl + '.release.json'), R / (pl + '.output_seal.json'),
              R / 'check_lean_owner_v4.py', R / 'verify_lean_metadata_v1.py', R / 'lean_budget_v5.py', Path(d['sealer']), *map(Path, history)]
    config('compile', inputs, [obj, obj.with_suffix('.ilean'), desc['compiler_stdout'], desc['compiler_stderr'], desc['kernel_receipt']],
           ['/usr/bin/python3.14', '-B', str(R / 'check_lean_owner_v4.py'), str(dp)],
           {'mathematical_input_identity': ident, 'expected_axiom_selectors': selectors})
else:
    raise AssertionError(mode)
