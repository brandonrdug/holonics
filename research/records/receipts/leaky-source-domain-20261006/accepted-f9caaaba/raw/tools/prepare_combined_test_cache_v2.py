"""Changed preparation read: test cache without unused incremental/example outputs."""
from pathlib import Path
import hashlib, json, resource, subprocess, sys, time
started = time.monotonic_ns()
d = json.loads(Path(sys.argv[1]).read_text())
q = Path(d['output_root'])
origin, cache = Path(d['cache_origin']), q / 'cache-v2'
assert not cache.exists()
def pin(p):
    p = Path(p); h = hashlib.sha256()
    with p.open('rb') as f:
        while b := f.read(2**20): h.update(b)
    return {'sha256': h.hexdigest(), 'bytes': p.stat().st_size}
def save(p, value):
    with p.open('x') as f: json.dump(value, f, indent=2); f.write('\n')
manifest_path = q / 'SOURCE_SNAPSHOT.v1.json'
assert pin(manifest_path) == d['source_manifest_pin']
manifest = json.loads(manifest_path.read_text())
source = Path(manifest['source_root'])
for rel, expected in manifest['source_inputs'].items():
    assert pin(source / rel) == expected, rel
assert set(manifest['source_inputs']) == {str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()}
assert pin(Path(d['owner_request'])) == d['owner_request_pin']
cache.mkdir(); (cache / 'debug').mkdir()
selected = d['cache_paths']
for rel in selected:
    subprocess.run(['/usr/bin/cp', '-a', '--reflink=always', str(origin / rel), str(cache / rel)], check=True)
files = {}
for p in sorted(cache.rglob('*')):
    if p.is_file():
        rel = str(p.relative_to(cache)); actual = pin(p)
        assert pin(origin / rel) == actual, rel
        files[rel] = actual
expected_members = set()
for rel in selected:
    path = origin / rel
    members = path.rglob('*') if path.is_dir() else [path]
    expected_members.update(str(p.relative_to(origin)) for p in members if p.is_file())
assert set(files) == expected_members
save(q / 'CACHE_SNAPSHOT.v2.json', {
    'origin': str(origin), 'cache_root': str(cache), 'selected_cache_paths': selected,
    'excluded_read': ['debug/incremental', 'debug/examples'],
    'reason': 'Declared test profile links current local source; unused incremental and old example executables are not consumed. Cargo may rebuild missing outputs under the unchanged build cap.',
    'files': files, 'count': len(files), 'total_bytes': sum(p['bytes'] for p in files.values()),
    'selected_full_reflinks_no_hardlinks': True, 'all_copies_byte_match_current_origin': True,
    'cached_objects_are_not_current_source_acceptance': True})
receipt = {'wall_ns': time.monotonic_ns() - started,
    'peak_RSS_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    'source_manifest': pin(manifest_path), 'current_source_verified': True,
    'cache_count': len(files), 'compiler_launched': False,
    'preserved_full_preparation_failure': d['preserved_failure']}
save(q / 'PREPARATION.v2.json', receipt)
print(json.dumps(receipt), flush=True)
