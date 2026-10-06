from pathlib import Path
import hashlib,json,subprocess,time,resource
R=Path(__file__).resolve().parent
Q=R/'physical-coupled-domain-20261006'
O=Path('/home/b/Workspaces/holonics/.local/wt/repair-field')
def ident(p):
 p=Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(2**20):h.update(b)
 return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def save(p,v):
 with p.open('x') as f:json.dump(v,f,indent=2);f.write('\n')
start=time.monotonic_ns();s=Q/'source-v3';c=Q/'cache-v3'
assert not s.exists() and not c.exists()
sealpath=O/'.local/physical-coupled-domain-20261006/source.seal.v3.json'
assert ident(sealpath)=={'bytes':950,'sha256':'729566a93abb96dbd89932fd840b8a40aecd6bb60ff1d35655d196da3b60f994'}
seal=json.loads(sealpath.read_text());prior=json.loads((Q/'SOURCE_DELTA.v2.json').read_text())
for rel,pin in prior['source_inputs'].items():assert ident(Q/'source-v2'/rel)==pin,rel
subprocess.run(['/usr/bin/cp','-a','--reflink=always',str(Q/'source-v2'),str(s)],check=True)
for row in seal['source']:
 p=O/row['path'];pin={k:row[k] for k in ('sha256','bytes')};assert ident(p)==pin
 subprocess.run(['/usr/bin/cp','--reflink=always',str(p),str(s/row['path'])],check=True)
 assert ident(p)==pin and ident(s/row['path'])==pin
sourcepins={str(p.relative_to(s)):ident(p) for p in sorted(s.rglob('*')) if p.is_file()}
subprocess.run(['/usr/bin/cp','-a','--reflink=always',str(Q/'cache-v1'),str(c)],check=True)
cachepins={}
for p in sorted(c.rglob('*')):
 if p.is_file():
  rel=str(p.relative_to(c));pin=ident(p);assert ident(Q/'cache-v1'/rel)==pin,rel;cachepins[rel]=pin
assert set(cachepins)=={str(p.relative_to(Q/'cache-v1')) for p in (Q/'cache-v1').rglob('*') if p.is_file()}
save(Q/'source.seal.v3.json',seal)
save(Q/'SNAPSHOT.v3.json',{'source_root':str(s),'source_inputs':sourcepins,'origin':str(O),'base':seal['base'],'owner_seal':ident(sealpath),'owner_source_unchanged':True,'prior_failures_preserved':True,'math_acceptance_unchanged':True})
save(Q/'CACHE_SNAPSHOT.v3.json',{'cache_root':str(c),'origin':str(Q/'cache-v1'),'files':cachepins,'count':len(cachepins),'total_bytes':sum(v['bytes'] for v in cachepins.values()),'full_reflink_without_hardlinks':True,'copies_byte_match_current_origin':True,'cached_local_objects_are_not_current_source_acceptance':True})
save(Q/'PREPARATION.v3.json',{'wall_ns':time.monotonic_ns()-start,'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_count':len(sourcepins),'cache_count':len(cachepins),'compiler_launched':False,'prior_source_and_cache_unmodified':True})
print(json.dumps({'prepared_source_count':len(sourcepins),'prepared_cache_count':len(cachepins),'wall_ns':time.monotonic_ns()-start}))
