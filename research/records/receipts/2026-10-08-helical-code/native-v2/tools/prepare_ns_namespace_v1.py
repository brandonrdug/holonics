"""Seal the actual full namespace closure, compressing proven prefix absences.

Uses the accepted sealer's byte/stamp contract and metadata verifier. It never
launches a compiler. Unlike the earlier preparation, it does not verify unused
upstream graph paths or probe every module below a prefix already proven absent.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import resource
import stat
import sys
import time

started = time.monotonic_ns()
desc = json.loads(Path(sys.argv[1]).read_text())
spec = importlib.util.spec_from_file_location('accepted_import_sealer', desc['sealer'])
seal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(seal)
events = []

def event(phase, beginning, **values):
    row = {'phase': phase, 'wall_ns': time.monotonic_ns() - beginning, **values}
    events.append(row)
    print(json.dumps(row), flush=True)

p = time.monotonic_ns()
cached = {}
known = {}
upstream_rows = 0
for graph_path in [desc['accepted_foreign_graph'], *desc['completed_metadata_graphs']]:
    graph = json.loads(Path(graph_path).read_text())
    upstream_rows += len(graph['file_records'])
    for path, row in graph['file_records'].items():
        if row['present']:
            stamp = row['target_stat']
            candidate = {k: stamp[k] for k in ['bytes', 'mtime_ns', 'ctime_ns']}
            candidate.update(path=path, present=True, sha256=row['sha256'])
            before = cached.get(path)
            if before is not None and before != candidate:
                raise seal.SealError('upstream present-file identities disagree: ' + path)
            cached[path] = candidate
    for row in graph['modules']:
        key = (row['module'], row['source_sha256'])
        if key in known and known[key] != row['imports']:
            raise seal.SealError('same-source parsed headers disagree: ' + row['module'])
        known[key] = row['imports']
    del graph
event('load only reusable source-SHA headers and present-part byte identities', p,
      upstream_path_rows_not_individually_validated=upstream_rows,
      reusable_present_paths=len(cached), reusable_headers=len(known))

object_roots = seal.ordered_unique(desc['object_roots'])
source_roots = seal.ordered_unique(desc['source_roots'])
records = {}
prefix_facts = {}
prefix_proofs = []
source_prefix_probes = []
source_candidate_probes = 0
prefix_inferred_absences = 0

def record(path, use_cache=True):
    return seal._record_unique(path, records, cached if use_cache else {})

def source_prefix(root, prefix):
    key = (str(root), prefix)
    if key not in prefix_facts:
        directory = record(root / prefix, False)
        top = record(root / (prefix + '.lean'))
        is_directory = bool(directory['target_stat'] and
                            stat.S_ISDIR(directory['target_stat']['mode']))
        prefix_facts[key] = (is_directory, top['present'])
        source_prefix_probes.append({'root': str(root), 'prefix': prefix,
            'directory_path': str(root / prefix), 'directory_present': is_directory,
            'top_file_path': str(root / (prefix + '.lean')), 'top_file_present': top['present']})
    return prefix_facts[key]

def resolve_source(name):
    global source_candidate_probes, prefix_inferred_absences
    prefix = name.split('.')[0]
    relative = seal.module_relpath(name, '.lean')
    probes = []
    for root in source_roots:
        directory, top = source_prefix(root, prefix)
        candidate = root / relative
        if (name != prefix and not directory) or (name == prefix and not top):
            prefix_inferred_absences += 1
            probes.append({'path': str(candidate), 'present': False,
                'absence_derived_from_prefix': str(root / prefix) if name != prefix
                    else str(root / (prefix + '.lean'))})
            continue
        source_candidate_probes += 1
        probe = seal.capture_resolution(candidate)
        probes.append(probe)
        record(candidate)
        if probe['present']:
            return candidate, probes
    raise seal.SealError('no source found in declared ordered lookup: ' + name)

object_namespaces = {}
def resolve_object(name):
    prefix = name.split('.')[0]
    if prefix not in object_namespaces:
        probes = []
        selected = None
        for root in object_roots:
            directory = record(root / prefix, False)
            top = record(root / (prefix + '.olean'))
            is_directory = bool(directory['target_stat'] and
                                stat.S_ISDIR(directory['target_stat']['mode']))
            probes.append({'root': str(root), 'directory_path': str(root / prefix),
                'directory_present': is_directory,
                'top_file_path': str(root / (prefix + '.olean')), 'top_file_present': top['present']})
            if is_directory or top['present']:
                selected = root
                break
        if selected is None:
            raise seal.SealError('no actual Lean namespace: ' + prefix)
        object_namespaces[prefix] = selected
        prefix_proofs.append({'prefix': prefix, 'selected_root': str(selected), 'ordered_probes': probes})
    selected = object_namespaces[prefix] / seal.module_relpath(name, '.olean')
    if not seal.capture_resolution(selected)['present']:
        raise seal.SealError('actual first namespace lacks imported module: ' + name + ': ' + str(selected))
    return selected

copied = json.loads(Path(desc['provider_namespace']).read_text())
provider_rows = {row['module']: row for row in copied['copies']}
seen = set()
modules = []
pending = [desc['target']]
reused = 0
parsed = 0
p = time.monotonic_ns()
while pending:
    name = pending.pop()
    if name in seen:
        continue
    seen.add(name)
    if name == desc['target']:
        source = Path(desc['source'])
        lookup = [{'path': str(source), 'present': True, 'selected': True}]
    else:
        source, lookup = resolve_source(name)
    source_record = record(source)
    if not source_record['present']:
        raise seal.SealError('selected source disappeared: ' + name)
    text = source.read_text()
    actual_sha = hashlib.sha256(text.encode()).hexdigest()
    if actual_sha != source_record['sha256']:
        raise seal.SealError('current source bytes differ from sealed identity: ' + name)
    header = known.get((name, actual_sha))
    if header is None:
        imports = seal.parse_imports(text, name)
        parsed += 1
    else:
        imports = header
        reused += 1
    if name == desc['target']:
        obj = None
        parts = {}
    else:
        obj = resolve_object(name)
        parts = {key: record(path) for key, path in seal._object_parts(obj).items()}
        provider = provider_rows.get(name)
        if provider is not None:
            if actual_sha != provider['source_pin']['sha256']:
                raise seal.SealError('accepted custom provider source differs: ' + name)
            for key, expected in provider['parts'].items():
                if not parts[key]['present'] or parts[key]['sha256'] != expected['pin']['sha256']:
                    raise seal.SealError('accepted custom provider part differs: ' + name + '/' + key)
    modules.append({'module': name, 'source_path': str(source), 'source_sha256': actual_sha,
        'source_lookup_precedence': lookup, 'selected_olean_path': str(obj) if obj else None,
        'object_lookup_precedence': [] if obj is None else [{'path': str(obj), 'present': True,
            'selection_derived_from_namespace_prefix': name.split('.')[0]}],
        'parts': parts, 'imports': imports})
    pending.extend(reversed(imports))
    if len(modules) % 1000 == 0:
        print(json.dumps({'phase': 'complete namespace closure progress', 'modules': len(modules),
                          'elapsed_ns': time.monotonic_ns() - p}), flush=True)
event('resolve and seal every consumed source and ordered object part', p, module_count=len(modules),
      bound_path_count=len(records), reused_headers=reused, freshly_parsed_headers=parsed)

p = time.monotonic_ns()
code_rows = {str(path): record(path) for path in desc['code_inputs']}
sealed = {'schema': 'holonics-complete-lean-import-parts-v1', 'target': desc['target'],
    'target_source': desc['source'], 'object_lookup_roots': [str(p) for p in object_roots],
    'source_lookup_roots': [str(p) for p in source_roots], 'module_count': len(modules),
    'modules': modules, 'code_inputs': code_rows, 'file_records': records,
    'hash_reuse_assumptions': seal.HASH_REUSE_ASSUMPTIONS,
    'ordered_namespace_prefix_proofs': prefix_proofs,
    'ordered_source_prefix_proofs': source_prefix_probes,
    'source_prefix_inferred_absence_count': prefix_inferred_absences,
    'source_candidate_file_probe_count': source_candidate_probes,
    'read_partition_change': 'Actual first Lean namespace once per prefix; ordered source ancestor absence once per prefix/root. Every selected source/part is still individually sealed. Unused historical upstream paths are excluded.',
    'parsed_graph_reuse': {'same_current_source_SHA256_required': True, 'reused_module_count': reused,
        'freshly_parsed_module_count': parsed, 'upstream_nonconsumed_path_reverification': False}}
nspec = importlib.util.spec_from_file_location('actual_namespace_lookup', desc['namespace_verifier'])
namespace = importlib.util.module_from_spec(nspec)
nspec.loader.exec_module(namespace)
namespace.verify_namespace_lookup(sealed)
sealed['actual_namespace_lookup_verified'] = True
changed = seal.verify_file_records(records)
if changed:
    raise seal.SealError('selected source/parts or prefix metadata changed: ' + str(changed[:8]))
event('independent namespace validation and complete selected metadata postcheck', p)
p = time.monotonic_ns()
with Path(desc['seal_output']).open('x') as output:
    json.dump(sealed, output, separators=(',', ':'))
    output.write('\n')
event('serialize complete reduced current graph', p, bytes=Path(desc['seal_output']).stat().st_size)
receipt = {'target': desc['target'], 'wall_ns': time.monotonic_ns() - started,
    'projection_ns': desc['preparation_projection_ns'],
    'peak_RSS_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    'module_count': len(modules), 'bound_path_count': len(records),
    'source_prefix_inferred_absence_count': prefix_inferred_absences,
    'complete_ordered_import_part_seal': True, 'actual_namespace_lookup_verified': True,
    'compiler_launched': False, 'events': events,
    'unused_upstream_paths_not_reverified': upstream_rows,
    'same_source_claims_and_resource_enforcement': True}
with Path(desc['preparation_receipt']).open('x') as output:
    json.dump(receipt, output, indent=2)
    output.write('\n')
print(json.dumps(receipt), flush=True)
