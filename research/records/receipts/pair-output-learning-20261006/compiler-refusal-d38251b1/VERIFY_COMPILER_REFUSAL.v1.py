from pathlib import Path
import hashlib,json,shutil,subprocess
root=Path.cwd()
archive=root/'research/records/receipts/pair-output-learning-20261006/native-validation-d38251b1-compiler-refusal'
dest=Path(__file__).resolve().parent
r=json.loads((archive/'VALIDATION.json').read_text())
head=r['source_commit']
def pin(b): return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def named(n):
 hits=[v for k,v in r['artifacts'].items() if k.endswith('/'+n)]
 assert len(hits)==1,n
 return (archive/hits[0]['copy']).read_bytes()
for name,v in r['artifacts'].items():
 assert pin((archive/v['copy']).read_bytes())=={k:v[k] for k in ('bytes','sha256')},name
s=json.loads(named('SOURCE_SNAPSHOT.v1.json'))
assert s['source_commit']==head and s['source_inputs']==r['source_inputs']
for name,want in s['source_inputs'].items():
 assert pin(subprocess.check_output(['git','show',head+':'+name]))==want,name
 assert pin((Path(s['source_root'])/name).read_bytes())==want,name
label='hnn-pair-learning-d38251b1-host-cuda-link-20261006-v1'
seal=json.loads(named(label+'.input_seal.json'))['inputs']
native={n:v for n,v in s['source_inputs'].items() if not n.startswith('lean/')}
for name,want in native.items(): assert seal[str(Path(s['source_root'])/name)]==want,name
stderr=named(label+'.stderr').decode()
assert stderr.count('error[E0609]')==1
assert 'no field `ticks` on type `hnn::word::EndChange`' in stderr
assert r['runtime_controls_launched']==0 and r['accepted'] is False
assert r['partial_artifacts_not_full_build_or_runtime_acceptance']
assert r['whole_unfiltered_output_preserved']
for label,stage in r['stages'].items():
 assert stage['quiescent_release'] and stage['outer_error'] is None
 assert stage['wall_ns']<=stage['projection_ns']
 assert stage['aggregate_CPU_ns']<=(128000000000 if 'host-cuda-link' in label else 17000000000)
 assert stage['group_peak_bytes']<=4294967296
 final=json.loads(named(label+'.final.json')); release=json.loads(named(label+'.release.json'))
 assert final['quiescent'] and final['aggregate_CPU_within_limit']
 assert release['released_after_final_publication_and_owned_unit_cleanup'] and release['quiescence_confirmed']
selected={}
for name,v in r['artifacts'].items():
 if '/admission-v1/hnn-pair-learning-d38251b1-' not in name: continue
 suffix=name.split('/admission-v1/',1)[1]
 if any(token in suffix for token in ('/cache-','/source-','/target/','/external/')): continue
 out=dest/'queue'/suffix; out.parent.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(archive/v['copy'],out); selected[str(out.relative_to(dest))]={k:v[k] for k in ('bytes','sha256')}
shutil.copyfile(archive/'VALIDATION.json',dest/'VALIDATION.json')
selected['VALIDATION.json']=pin((dest/'VALIDATION.json').read_bytes())
summary=dict(source_commit=head,source_base=r['source_base'],all_original_artifacts_rehashed=len(r['artifacts']),original_artifact_bytes=sum(v['bytes'] for v in r['artifacts'].values()),source_snapshot_and_git_inputs_verified=len(s['source_inputs']),native_build_bindings_verified=len(native),accepted=False,runtime_controls_launched=0,exact_compiler_error=r['source_error'],stages=r['stages'],all_caps_and_cleanup_pass=True,partial_compiler_artifacts_are_not_native_acceptance=True,selected_preserved_artifacts=selected,large_binaries_toolchain_cache_not_committed=True,scientific_job=False,GPU_runtime=False,unchanged_Lean_not_recompiled=True)
(dest/'COMPILER_REFUSAL_JOIN.v1.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['selected_preserved_artifacts','stages']},indent=2))
print('Preserved',len(selected),'compact artifacts,',sum(v['bytes'] for v in selected.values()),'bytes.')
