"""Frozen native duplex source and bounded stages; no scientific source edits."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, sys

R=Path(__file__).resolve().parent
ROOT=R.parents[2]
L=R/'helical-duplex-20261009-v132'
S=L/'source-v2'
COMMIT='02658c6c2ddaf94b0bf66eb9c7db91307f1fc2ce'
OLD='c6fcc82a187174333ca494bf35c1c8cb7062ab56'
RUNNERS=[R/n for n in ['final_stage_memory_v120.py','leased_stage_memory_v120.py','bounded_stage_memory_v120.py']]
def read(p):return json.loads(Path(p).read_text())
def save(p,v):
    with Path(p).open('x') as f:json.dump(v,f,indent=2);f.write('\n')
def pin(p):
    p=Path(p);h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(2**20):h.update(b)
    return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args])
def config(mode):
    ad=read(L/'SOURCE_ADMISSION.json')
    native=L/'SOURCE_NATIVE_INPUTS.json'
    source=[S/p for p in ad['source_inputs']]
    common=source+[Path(__file__),L/'SOURCE_ADMISSION.json',native]+RUNNERS
    if mode=='prepare':
        d={'output_root':str(L),'cache_partitions':[{'origin':str(R/'integration-c6-targeted-20261008-v120/cache-v2'),'paths':['debug/deps','debug/build','debug/.fingerprint','.rustc_info.json']}],'source_snapshot_path':str(native),'source_manifest_pin':pin(native),'owner_request':str(L/'SOURCE_ADMISSION.json'),'owner_request_pin':pin(L/'SOURCE_ADMISSION.json'),'preserved_failure':'Original c6fcc82a source is preserved and unexecuted; review defects corrected in 02658c6c. All prior queue receipts remain immutable.'}
        dp=L/'PREPARATION_REQUEST.json';save(dp,d)
        c=read(R/'integration-c6-cache-prep-20261008-v120.config.json')
        label='helical-duplex-cache-prep-20261009-v132'
        inputs=common+[dp,R/'prepare_joined_cache_v111.py',Path('/usr/bin/cp'),Path('/usr/bin/python3.14')]
        expected={str(p.resolve()):pin(p) for p in inputs}
        c.update(argv=['/usr/bin/python3.14','-B',str(R/'prepare_joined_cache_v111.py'),str(dp)],outputs=[str(L/'CACHE_SNAPSHOT.v2.json'),str(L/'PREPARATION.v2.json')],input_directories=[],allocation_basis={'largest_matching_preparation_wall_ns':9631500123,'fixed_window_ns':17000000000,'separate_from_compilation':True})
    else:
        prep='helical-duplex-cache-prep-20261009-v132'
        assert read(R/(prep+'.acceptance.json'))['passed'] and read(R/(prep+'.release.json'))['quiescence_confirmed']
        cache=L/'cache-v2'
        if mode=='build':
            preserve=L/'preserved-local-fingerprints';preserve.mkdir()
            for p in sorted((cache/'debug/.fingerprint').iterdir()):
                if p.is_dir() and p.name.startswith(('holonics-','holonics-cuda-')):shutil.move(str(p),str(preserve/p.name))
            template='integration-c6-lib-build-20261008-v120'
        else:template={'check':'integration-faa8-workspace-all-targets-check-20261008-v2','clippy':'integration-faa8-all-targets-guard-lints-20261008-v2','doc':'integration-faa8-guard-doctests-20261008-v2'}[mode]
        c=read(R/(template+'.config.json'))
        foreign={p:v for p,v in c['expected_inputs'].items() if p.startswith(('/usr/bin/','/home/b/.rustup/','/home/b/.cargo/','/opt/cuda/'))}
        inputs=common+[Path(p) for p in foreign]+[R/(prep+'.'+ext) for ext in ['config.json','acceptance.json','release.json','output_seal.json']]+[L/'CACHE_SNAPSHOT.v2.json',L/'PREPARATION.v2.json']
        expected={**foreign,**{str(p.resolve()):pin(p) for p in inputs if str(p) not in foreign}}
        c['input_directories']=[p for p in c['input_directories'] if not p.startswith(str(ROOT))]
        av=[]
        for p in c['argv']:
            if p.startswith('CARGO_TARGET_DIR='):p='CARGO_TARGET_DIR='+str(cache)
            elif p in ('RAYON_NUM_THREADS=8','CARGO_BUILD_JOBS=8'):p=p[:-1]+'1'
            elif p=='-j8':p='-j1'
            av.append(p)
        if mode=='doc':av.insert(av.index('/usr/bin/timeout'),'RUST_TEST_THREADS=1')
        label='helical-duplex-'+mode+'-20261009-v132'
        c.update(argv=av,outputs=[],stage_kind='native_compile',projection_ns=65000000000,aggregate_cpu_limit_us=128000000,aggregate_cpu_stop_margin_us=4000000,group_memory_max_bytes=2**33,address_space_max_bytes=-1,minimum_MemAvailable_KiB=12*2**20,thread_budget=1,explicit_user_8GiB_authorization=True,explicit_user_workload_duration_authorization=True,allocation_basis={'largest_prior_alltest_compile_wall_ns':56663442597,'largest_prior_native_unit_wall_ns':64890000000,'fixed_existing_compile_window_ns':65000000000,'aggregate_CPU_us':128000000,'one_CPU_affinity_and_Cargo_jobs':1,'profile_preserved':True,'new_elaboration_unmeasured':True,'parent_authorization':'Existing 8 GiB ceiling; workload-based fixed time, sole queue; no broad HNN runtime.'})
    # Drop inherited descriptions of unrelated tasks while preserving resource/guard fields.
    for k in ['queue_order','compiler_partition_choice','confirmed_resource_handoff','source_binding_repair','read_partition_change','launch_pending_resource_owner_handoff']:c.pop(k,None)
    c.update(label=label,scope_unit='holonics-prune-admission-'+label,cwd=str(ROOT if mode=='prepare' else S),scope='Frozen corrected native duplex 02658c6c; '+mode+' only; no HNN science, GPU or Lean rerun',source_commit=COMMIT,source_base=OLD,inputs=list(dict.fromkeys(map(str,inputs))),expected_inputs=expected,unchanged_resource_caps=True)
    save(R/(label+'.config.json'),c);print(label,flush=True)

mode=sys.argv[1]
if mode=='source':
    L.mkdir();S.mkdir()
    tree=git('rev-parse',COMMIT+'^{tree}').decode().strip();assert tree=='ca41addd4277ab5d74bfb23c8a84077486161380'
    assert git('rev-parse',COMMIT+'^').decode().strip()==OLD
    subprocess.run(['git','-C',str(ROOT),'merge-base','--is-ancestor','6ddcab6d5ac583221ad6bdd067e6ff97f9bb628e',COMMIT],check=True)
    prior=read(ROOT/'.local/lean-rust-pruning/c6-source-worker-20261008/SOURCE_ADMISSION.json')
    entries={}
    for row in git('ls-tree','-r','-z',COMMIT).split(b'\0'):
        if not row:continue
        head,path=row.split(b'\t',1);modebits,kind,blob=head.decode().split();rel=path.decode()
        if rel.startswith(('crates/','research/notebook/','accelerators/')) or rel in prior['source_inputs']:
            assert kind=='blob' and modebits!='120000';entries[rel]=blob
    pins={};full={}
    for rel,blob in sorted(entries.items()):
        b=git('cat-file','blob',blob);p=S/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
        pins[rel]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};full[rel]={**pins[rel],'git_blob':blob}
    required={'crates/holonics/src/compression/keys/duplex.rs':'48f7f660e3a35896176a8b723fae44a043cd0920ed0935ed451642498f75615d','crates/holonics/src/compression/keys/duplex/tests.rs':'1f3a651be1952fb7f24a4d79c446ff14ff2aa201609d0e5eaa2897bc5ab9875a','crates/holonics/src/compression/keys/transport.rs':'f722ebaede27d335dfb1f8d7b7c0d7794339619522faefa749c9922a246a057a','crates/holonics/src/compression/keys.rs':'5c241a8f46b49af925e5dc37633bb1667315006a048ba8a2564cb87e5fd6c154'}
    assert all(pins[p]['sha256']==h for p,h in required.items())
    atlas=git('show',COMMIT+':docs/atlas/geometry.tsv');assert hashlib.sha256(atlas).hexdigest()=='89bb8869ea5ceea1972ef853aa8f48c18e7bcd33a4aff05ff26b9274d9df6612';(L/'geometry.tsv').write_bytes(atlas)
    old=L/'original-unexecuted-source';old.mkdir()
    for rel in list(required)+['docs/atlas/geometry.tsv']:
        p=old/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(git('show',OLD+':'+rel))
    tests=(S/'crates/holonics/src/compression/keys/duplex/tests.rs').read_text()
    names=re.findall(r'#\[test\]\s*fn\s+(\w+)\(',tests);assert len(names)==21 and len(set(names))==21
    ad={'source_commit':COMMIT,'source_tree':tree,'source_base':OLD,'source_root':str(S),'source_inputs':full,'test_selectors':['compression::keys::duplex::tests::'+n for n in names],'frozen_git_bytes':True,'original_source_unexecuted':True,'required_gate1': ['workspace --all-targets check','holonics --all-targets disallowed/float clippy','holonics guard doctests'],'scope':'Declared local-factor/Markov-fit known-truth duplex composition; no learned key discovery, generalization, material power, continuing HNN partner or ribbon geometry claim'}
    save(L/'SOURCE_ADMISSION.json',ad);save(L/'SOURCE_NATIVE_INPUTS.json',{**ad,'source_inputs':pins})
    print(json.dumps({'native_files':len(pins),'source_bytes':sum(p['bytes'] for p in pins.values()),'selectors':len(names),'commit':COMMIT}))
else:config(mode)
