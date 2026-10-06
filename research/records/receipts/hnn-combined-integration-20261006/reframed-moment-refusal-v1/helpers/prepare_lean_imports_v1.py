"""Prepare complete lookup/part seals using the accepted import sealer.

The already accepted foreign graph supplies parsed headers only when the current
source text has the same SHA256. New headers are parsed, and every selected file
and leading lookup absence is bound through the existing sealer. No compiler.
"""
from pathlib import Path
import hashlib, importlib.util, json, resource, sys, time
started = time.monotonic_ns()
desc = json.loads(Path(sys.argv[1]).read_text())
spec = importlib.util.spec_from_file_location('accepted_import_sealer', desc['sealer'])
seal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(seal)
baseline = json.loads(Path(desc['accepted_foreign_graph']).read_text())
cached = {}
def add_cache(records):
    for path, row in records.items():
        if row['present']:
            st = row['target_stat']
            cached[path] = {k:st[k] for k in ['bytes','mtime_ns','ctime_ns']}
            cached[path].update(path=path, present=True, sha256=row['sha256'])
        elif not row['exists']:
            cached[path] = {'path':path,'present':False}
add_cache(baseline['file_records'])
for path in desc.get('preflights', []):
    pre = json.loads(Path(path).read_text())
    changed = seal.verify_file_records(pre['file_records'])
    assert not changed, ('preflight inputs changed', changed[:8])
    add_cache(pre['file_records'])
known = {row['module']:row for row in baseline['modules']
         if not row['module'].startswith('Holonics.')}
original_parser = seal.parse_imports
reused, parsed = [], []
def parse_imports(text, module):
    row = known.get(module)
    if row and hashlib.sha256(text.encode('utf8')).hexdigest() == row['source_sha256']:
        reused.append(module)
        return row['imports']
    parsed.append(module)
    return original_parser(text, module)
seal.parse_imports = parse_imports
sealed = seal.seal_modules(desc['target'], desc['source'], desc['object_roots'],
                           desc['source_roots'], desc['code_inputs'], cached)
changed = seal.verify_file_records(sealed['file_records'])
assert not changed, ('prepared files changed', changed[:8])
sealed['parsed_graph_reuse'] = {'accepted_graph':desc['accepted_foreign_graph'],
    'same_current_source_SHA256_required':True, 'reused_module_count':len(reused),
    'freshly_parsed_module_count':len(parsed)}
with Path(desc['seal_output']).open('x') as f:
    json.dump(sealed, f, separators=(',',':'));f.write('\n')
wall = time.monotonic_ns()-started
receipt = {'target':desc['target'], 'wall_ns':wall,
           'projection_ns':desc['preparation_projection_ns'],
           'measured_to_projected_ratio':[wall,desc['preparation_projection_ns']],
           'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
           'module_count':sealed['module_count'],
           'parsed_graph_reuse':sealed['parsed_graph_reuse'],
           'complete_ordered_import_part_seal':True, 'compiler_launched':False}
with Path(desc['preparation_receipt']).open('x') as f:
    json.dump(receipt,f,indent=2);f.write('\n')
print(json.dumps(receipt),flush=True)
