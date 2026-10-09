"""Preserve the complete source-bound acceptance packet without publishing Git changes."""
from pathlib import Path
import hashlib, json, shutil, subprocess

R=Path(__file__).resolve().parent;ROOT=R.parents[2];L=R/'helical-duplex-20261009-v132'
D=ROOT/'research/records/receipts/2026-10-09-helical-duplex/native-v2'
def read(p):return json.loads(Path(p).read_text())
def pin(p):
    p=Path(p);h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(2**20):h.update(b)
    return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def save(p,v):
    with Path(p).open('x') as f:json.dump(v,f,indent=2);f.write('\n')
units=['cache-prep','check','build','runtime-index','runtime-binding','runtime-development','runtime-acceptance','clippy','doc']
results=[]
for u in units:
    label='helical-duplex-'+u+'-20261009-v132'
    assert read(R/(label+'.acceptance.json'))['passed'] and read(R/(label+'.release.json'))['quiescence_confirmed']
    f=read(R/(label+'.final.json'));p=read(R/(label+'.publication.json'));c=read(R/(label+'.config.json'))
    results.append({'unit':u,'label':label,'accepted':True,'quiescence_confirmed':True,'wall_ns':f['wall_ns'],'projection_ns':f['projection_ns'],'measured_to_projected':{'numerator':f['wall_ns'],'denominator':f['projection_ns']},'aggregate_CPU_ns':f['final_CPU_ns'],'aggregate_CPU_limit_us':f['aggregate_CPU_limit_us'],'group_peak_bytes':int(f['unit_properties']['MemoryPeak']),'child_peak_RSS_KiB':p['outcome']['peak_child_RSS_KiB'],'CPU_affinity_count':c['thread_budget'],'group_memory_ceiling_bytes':c['group_memory_max_bytes']})
assert read(L/'acceptance.RUNTIME_RESULT.json')['native_exit']==0
events=read(L/'acceptance.RUNTIME_RESULT.json')['events'];assert len(events)==21 and all(e['result']=='ok' for e in events)
doc=(R/'helical-duplex-doc-20261009-v132.stdout').read_text()
assert 'test result: ok.' in doc and '0 failed' in doc
doc_summary=[line for line in doc.splitlines() if line.startswith(('running ','test result:'))]
ad=read(L/'SOURCE_ADMISSION.json');exe=Path(read(L/'COMPILED_LIB.json')['row']['executable'])
assert pin(exe)==read(L/'COMPILED_LIB.json')['executable_pin']
D.mkdir(parents=True)
copied={}
def copy(p,rel):
    q=D/rel;q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists()
    subprocess.run(['/usr/bin/cp','--reflink=always',str(p),str(q)],check=True)
    a=pin(p);assert pin(q)==a;copied[str(rel)]=a
for u in units:
    label='helical-duplex-'+u+'-20261009-v132'
    for p in sorted(R.glob(label+'.*')):
        if p.is_file():copy(p,Path('stages')/p.name)
for p in sorted(L.rglob('*')):
    if p.is_file() and not p.is_relative_to(L/'cache-v2') and not p.is_relative_to(L/'preserved-local-fingerprints'):
        copy(p,Path('admission')/p.relative_to(L))
for name in ['materialize_duplex_v132.py','materialize_duplex_runtime_v132.py','stream_duplex_runtime_v132.py','prepare_joined_cache_v111.py','final_stage_memory_v120.py','leased_stage_memory_v120.py','bounded_stage_memory_v120.py','package_duplex_v132.py']:
    copy(R/name,Path('queue-source')/name)
copy(exe,Path('compiled')/'holonics-duplex-tests')
validation={'source_commit':ad['source_commit'],'source_tree':ad['source_tree'],'predecessor_commit':ad['source_base'],'original_bundle_preserved_unexecuted':True,'corrected_contracts':['malformed partner indices including usize::MAX refuse before reversal arithmetic','receiver binds its producing LocatedTransport; equal helix with changed advances refuses'],'native_source_file_count':len(ad['source_inputs']),'native_test_count':21,'expected_test_names':read(L/'acceptance.RUNTIME_RESULT.json')['expected_names'],'all_native_tests_passed':True,'required_gate1_passed':True,'doc_summary':doc_summary,'fresh_test_executable':read(L/'COMPILED_LIB.json'),'results':results,'claim_scope':ad['scope'],'not_accepted':['learned key discovery or generalization to unseen constitutions','full damage-channel correction; coordinated complementary damage remains outside coverage','physical material power or continuing HNN partner return','located-clock face geometry or ribbon/Lk=Tw+Wr geometry'],'publication':'Local receipt files only. No push, merge, history rewrite, worktree removal or scientific source mutation.'}
save(D/'VALIDATION.json',validation)
lines=['# Corrected native duplex acceptance','',f"Source `{ad['source_commit']}`, tree `{ad['source_tree']}`. Original `{ad['source_base']}` is preserved and was not executed.",'','All 21 exact duplex tests passed from a fresh source-bound library-test executable. The required workspace all-targets check, all-targets exact-arithmetic guard lints and full library guard doctests passed. '+ '; '.join(doc_summary)+'.','','The two source-review corrections are consumed by actual regressions: malformed partner contacts 3 and usize::MAX on length 3 return IndexOutside before reversal arithmetic; a receiver founded on one transport refuses a changed advance on the same helix, while each matching pair succeeds.','','| Unit | Wall ns | Fixed projection ns | Aggregate CPU ns | Group peak B | Child peak RSS KiB |','|---|---:|---:|---:|---:|---:|']
for x in results:lines.append(f"| {x['unit']} | {x['wall_ns']} | {x['projection_ns']} | {x['aggregate_CPU_ns']} | {x['group_peak_bytes']} | {x['child_peak_RSS_KiB']} |")
lines+=['','Every stage used the existing sole lease, one CPU affinity, fixed CPU/wall bounds and unchanged authorized ceilings. Compilation retained the prior 65,000,000,000 ns native unit window and 128,000,000 us aggregate CPU ceiling. Cache preparation remained a separate 17,000,000,000 ns / 4,294,967,296 B unit. Runtime acceptance was fixed before launch at 21 × 1,472,265,594 ns = 30,917,577,474 ns, the maximum measured development-unit wall. Each native test completed below that unit upper. Every final acceptance has matching owned cleanup and quiescent lease-release receipts. No cap ladder or unchanged failed rerun occurred.','','Actual known-truth outputs: text/pitch/levels free families released 3/0/3 and held 21/24/21 of 24 each. Complete enumeration covered 92/134/108 members, with exact coordinate-max diameter and actual attaining witnesses. Coordinated complementary damage slipped zero contacts and released all its one-member families; against known truth it absorbed 16/12/11 and left residual 152/540/349. These residuals are outside channel coverage.','','Acceptance is limited to the reviewed declared local-factor/Markov-fit known-truth composition. It does not establish learned key discovery, generalization, exhaustive channel correction, physical material power, continuing HNN partner return or ribbon geometry. The earlier accepted Lean seal remains independent; it was not rerun.','','Whole native outputs: [stdout](admission/acceptance.native.stdout), [stderr](admission/acceptance.native.stderr). Source, exact fixtures, executable, cache provenance, raw diagnostics, timing/resource receipts and original unexecuted source are preserved here. [Machine-readable validation](VALIDATION.json).','','No source edits, push, merge, history rewrite, branch/worktree deletion or broad HNN/GPU/scientific execution was performed.']
(D/'HANDOFF.md').write_text('\n'.join(lines)+'\n')
copied['VALIDATION.json']=pin(D/'VALIDATION.json');copied['HANDOFF.md']=pin(D/'HANDOFF.md')
save(D/'FILE_HASHES.json',{'files':copied,'count':len(copied),'total_bytes':sum(p['bytes'] for p in copied.values()),'all_reflink_copies_byte_verified':True})
print(json.dumps({'handoff':str(D/'HANDOFF.md'),'files':len(copied),'bytes':sum(p['bytes'] for p in copied.values()),'Gate1':True,'native_tests':21,'doc_summary':doc_summary}))
