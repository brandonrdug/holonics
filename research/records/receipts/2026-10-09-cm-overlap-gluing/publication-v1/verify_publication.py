#!/usr/bin/env python3
"""Verify public source/provenance bindings; this does not invoke Lean."""
import hashlib
import json
import re
import resource
import subprocess
import time
from pathlib import Path

start = time.perf_counter_ns()
root = Path(__file__).resolve().parents[5]
packet = Path('research/records/receipts/2026-10-09-cm-overlap-gluing')
pub = packet / 'publication-v1'

def read(path):
    return json.loads((root / path).read_text())

def pin(path):
    b = (root / path).read_bytes()
    return {'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}

seals = read(pub / 'FILE_SEALS.json')
for item in seals:
    assert pin(item['path']) == {k: item[k] for k in ['sha256', 'bytes']}, item['path']
    data = (root / item['path']).read_bytes()
    for forbidden in [b'/' + b'home/', b'/' + b'tmp/', b'codex_' + b'delegation',
                      b'source_' + b'thread_id', b'agent-' + b'mailbox/messages']:
        assert forbidden not in data, (item['path'], forbidden)

provenance = read(pub / 'PROVENANCE.json')
for artifact in provenance['artifact_mapping']:
    assert pin(artifact['published_path']) == artifact['published'], artifact['published_path']
    if artifact['transform'] == 'exact bytes':
        assert artifact['original'] == artifact['published']
targets = provenance['accepted_targets']
owner = packet / 'v9/source-v9/CMActualGraphDiagonalAnalyticCut.lean'
importer = packet / 'v9/source-v9/CMActualGraphDiagonalAnalyticCutAudit.lean'
assert pin(owner)['sha256'] == '2b213f4bcad6cd8bd466729ed9abbb32fecf378526a4cae786b5220c1251fc79'
assert pin(importer)['sha256'] == '61c683a8eaf8c29891072b6d385babf1795e93d9cb8739e1483fc8ba23a77a8e'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, source, count in [('CMActualGraphDiagonalAnalyticCut', owner, 59),
                             ('CMActualGraphDiagonalAnalyticCutAudit', importer, 7)]:
    queries = re.findall(r'^#print axioms (.*)$', (root / source).read_text(), re.M)
    assert len(queries) == count
    v = read(targets[name]['validation'])
    k = read(targets[name]['kernel'])
    assert v['kernel_accepted'] and k['kernel_accepted']
    assert v['compiler_exit'] == k['compiler_exit'] == 0
    assert v['queries_required'] == v['queries_reached'] == count
    assert not v['nonstandard_queries'] and not v['meaningful_error_records']
    assert set(v['all_query_results']) == {'Holonics.Hodge.CMGraphSource.' + x for x in queries}
    assert all(set(axioms) <= allowed for axioms in v['all_query_results'].values())

providers = read(pub / 'PROVIDER_BINDINGS.json')['providers']
assert len(providers) == 117
for provider in providers:
    assert pin(provider['publication_source']) == provider['source_pin']
base_entries = None
for role, expected in [('owner', 5119), ('importer', 5120)]:
    binding = read(pub / ('SELECTED_IMPORT_BINDINGS.' + role + '.json'))
    if role == 'owner':
        entries = {x['module']: x for x in binding['all_selected_sources_parts_and_import_edges']}
        base_entries = entries
    else:
        overlay = binding['exact_binding_overlay']
        assert overlay['base'] == 'SELECTED_IMPORT_BINDINGS.owner.json'
        entries = dict(base_entries)
        for name in overlay['removed']:
            del entries[name]
        entries.update({x['module']: x for x in overlay['replaced'] + overlay['added']})
        assert sum(item == entries.get(name) for name, item in base_entries.items()) == overlay['unchanged_base_entries']
    assert len(entries) == binding['module_count'] == expected
    for item in entries.values():
        assert all(dep in entries for dep in item['imports']), item['module']
        if 'publication_source' in item:
            assert pin(item['publication_source'])['sha256'] == item['source_sha256']
    for provider in providers:
        item = entries[provider['module']]
        for part, partpin in provider['selected_parts'].items():
            assert item['parts'][part]['sha256'] == partpin['sha256']
    if role == 'importer':
        assert entries['CMActualGraphDiagonalAnalyticCut']['parts']['main']['sha256'] == \
            targets['CMActualGraphDiagonalAnalyticCut']['object_pins']['olean']['sha256']

join = read(packet / 'NATIVE_JOIN.v9.json')
assert join['source_sha256'] == pin(owner)['sha256']
for role in ['owner', 'importer']:
    assert (root / join[role]['receipt']).is_file()
assert not join['full_library_checked']
assert provenance['remaining_obligations'] == join['remaining_obligations']

# The shared indexes are checked by content, not as whole files: other publications add their own
# rows and routes to them (INTEGRATION.json). The publication base stays the historical provenance.
atlas = read(pub / 'ATLAS_JOIN.json')
integration = read(pub / 'INTEGRATION.json')
assert integration['publication_base_commit'] == provenance['publication_base_commit']
assert not integration['source_changed']
current = (root / 'docs/atlas/targets.tsv').read_text().splitlines()
ids = [x.split('\t')[0] for x in current if x]
assert set(atlas['keys']) == {row.split('\t')[0] for row in atlas['rows']}
for row in atlas['rows']:
    assert current.count(row) == 1, row.split('\t')[0]
    assert ids.count(row.split('\t')[0]) == 1, row.split('\t')[0]
index = (root / 'research/records/README.md').read_text().splitlines()
for route in integration['index_routes']:
    assert index.count(route) == 1, route[:80]
    for target in re.findall(r'\]\(([^)]+)\)', route):
        if not target.startswith(('https:', 'http:', '#')):
            assert (root / 'research/records' / target.split('#')[0]).exists(), target
for item in seals:
    path = root / item['path']
    if path.suffix == '.md':
        content = path.read_text()
        for target in re.findall(r'\]\(([^)]+)\)', content):
            if target.startswith(('https:', 'http:', '#')):
                continue
            assert (path.parent / target.split('#')[0]).exists(), (item['path'], target)

receipt = {'status': 'PASS exact public source, acceptance, provider/import and atlas/index bindings',
           'sealed_files_verified': len(seals), 'providers': 117,
           'owner_queries': 59, 'importer_queries': 7,
           'selected_import_modules': {'owner': 5119, 'importer': 5120},
           'native_or_library_jobs_launched': False,
           'canonical_relocation_checked': False,
           'publication_base_commit': provenance['publication_base_commit'],
           'integration_base_commit': integration['integration_base_commit'],
           'shared_indexes_checked_by_content': integration['shared_indexes_checked_by_content'],
           'projection_ns': 7482721030,
           'measured_wall_ns': time.perf_counter_ns() - start,
           'peak_resident_bytes': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024}
assert receipt['measured_wall_ns'] < receipt['projection_ns']
(root / pub / 'INTEGRATION_CHECK.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
