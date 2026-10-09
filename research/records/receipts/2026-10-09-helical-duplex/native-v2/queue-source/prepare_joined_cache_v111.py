"""Selected debug/release cache partitions, byte sealed under the existing guard."""
from pathlib import Path
import hashlib,json,resource,subprocess,sys,time
t=time.monotonic_ns();d=json.loads(Path(sys.argv[1]).read_text());q=Path(d['output_root']);cache=q/'cache-v2';assert not cache.exists()
def pin(p):
    p=Path(p);h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(2**20):h.update(b)
    return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def save(p,v):
    with p.open('x') as f:json.dump(v,f,indent=2);f.write('\n')
mp=Path(d['source_snapshot_path']);assert pin(mp)==d['source_manifest_pin'];m=json.loads(mp.read_text());s=Path(m['source_root'])
for rel,e in m['source_inputs'].items():assert pin(s/rel)==e
assert set(m['source_inputs'])=={str(p.relative_to(s)) for p in s.rglob('*') if p.is_file()}
assert pin(d['owner_request'])==d['owner_request_pin']
cache.mkdir();files={};members=set();origins={}
for part in d['cache_partitions']:
    origin=Path(part['origin'])
    for rel in part['paths']:
        assert not (cache/rel).exists();(cache/rel).parent.mkdir(exist_ok=True,parents=True)
        subprocess.run(['/usr/bin/cp','-a','--reflink=always',str(origin/rel),str(cache/rel)],check=True)
        p=origin/rel
        for f in (p.rglob('*') if p.is_dir() else [p]):
            if f.is_file():
                key=str(f.relative_to(origin));assert key not in members;members.add(key);origins[key]=f
for p in sorted(cache.rglob('*')):
    if p.is_file():
        rel=str(p.relative_to(cache));actual=pin(p);assert pin(origins[rel])==actual;files[rel]=actual
assert set(files)==members
save(q/'CACHE_SNAPSHOT.v2.json',{'cache_root':str(cache),'cache_partitions':d['cache_partitions'],
    'files':files,'count':len(files),'total_bytes':sum(e['bytes'] for e in files.values()),
    'all_copies_byte_match_current_origin':True,'full_reflinks_no_hardlinks':True,
    'mutable_local_targets_require_current_source_compilation_or_verified_exact_accepted_scope':True})
receipt={'wall_ns':time.monotonic_ns()-t,'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    'source_manifest':pin(mp),'current_source_verified':True,'cache_count':len(files),'compiler_launched':False,'preserved_failure':d['preserved_failure']}
save(q/'PREPARATION.v2.json',receipt);print(json.dumps(receipt),flush=True)
