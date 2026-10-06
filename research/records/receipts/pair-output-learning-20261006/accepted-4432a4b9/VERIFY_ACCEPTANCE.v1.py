from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path.cwd();dest=Path(__file__).resolve().parent
archive=root/'research/records/receipts/pair-output-learning-20261006/native-validation-4432a4b9'
r=json.loads((archive/'VALIDATION.json').read_text());head=r['source_commit']
def pin(b):return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def named(n):
 hits=[v for k,v in r['artifacts'].items() if k.endswith('/'+n)]
 assert len(hits)==1,n
 return (archive/hits[0]['copy']).read_bytes()
for n,v in r['artifacts'].items():assert pin((archive/v['copy']).read_bytes())=={k:v[k] for k in ('bytes','sha256')},n
s=json.loads(named('SOURCE_SNAPSHOT.v1.json')); assert s['source_commit']==head and s['source_inputs']==r['source_inputs']
for n,want in s['source_inputs'].items():
 assert pin(subprocess.check_output(['git','show',head+':'+n]))==want,n
 assert pin((Path(s['source_root'])/n).read_bytes())==want,n
native={n:v for n,v in s['source_inputs'].items() if not n.startswith('lean/')}
label='hnn-pair-learning-4432a4b9-host-cuda-link-20261006-v1'
compiled=json.loads(named('COMPILED_ARTIFACTS.v1.json'))['artifacts']
cargo=[json.loads(l) for l in named(label+'.stdout').decode().splitlines() if l.startswith('{')]
local=[a for a in cargo if a.get('reason')=='compiler-artifact' and 'path+file://' in a.get('package_id','')]
assert compiled and all(a['fresh'] is False for a in compiled)
assert [{k:v for k,v in a.items() if k!='executable_pin'} for a in compiled]==local
host=next(a for a in compiled if a['target']['name']=='holonics' and a['profile']['test'] and a.get('executable'))
assert host['executable_pin']==r['compiled_source_binding']['new_holonics_executable_pin']
assert pin((archive/r['artifacts'][host['executable']]['copy']).read_bytes())==host['executable_pin']
actual=[]
for run in r['runtime_results']:
 label=run['label'];assert run['passed'] and run['quiescent'] and not run['issues']
 raw=named(label+'.stdout').decode();names=re.findall(r'^test (\S+) \.\.\.',raw,re.M)
 assert names==run['actual_test_names'] and len(names)==run['expected_tests'],label
 assert re.search(r'test result: ok\. '+str(len(names))+r' passed; 0 failed; 0 ignored;',raw),label
 actual.extend(names);seal=json.loads(named(label+'.input_seal.json'))['inputs']
 for n,want in native.items():assert seal[str(Path(s['source_root'])/n)]==want,(label,n)
assert len(actual)==len(set(actual))==26 and sorted(actual)==sorted(r['actual_test_names'])
assert len(r['runtime_results'])==16
seal=json.loads(named('hnn-pair-learning-4432a4b9-host-cuda-link-20261006-v1.input_seal.json'))['inputs']
for n,want in native.items():assert seal[str(Path(s['source_root'])/n)]==want,n
for label,stage in r['stages'].items():
 assert stage['accepted'] and stage['quiescent_release'] and stage['outer_error'] is None
 assert stage['wall_ns']<=stage['projection_ns']
 assert stage['aggregate_CPU_ns']<=(128000000000 if 'host-cuda-link' in label else 17000000000)
 assert stage['group_peak_bytes']<=4294967296
effects=json.loads(named('MATCHED_PAIR_OUTPUT_EFFECTS.v1.json'))
assert effects['source_commit']==head
assert pin(named('hnn-pair-learning-4432a4b9-control-group15-20261006-v1.stdout'))==effects['raw_pin']
assert effects['same_gap_fibre_all_six']==[0,2,3]
assert effects['source_arrangement_sensitivity_changes_in_logits']
selected={}
for n,v in r['artifacts'].items():
 if '/admission-v1/hnn-pair-learning-4432a4b9-' not in n:continue
 suffix=n.split('/admission-v1/',1)[1]
 if any(t in suffix for t in ('/cache-','/source-','/target/','/external/')):continue
 out=dest/'queue'/suffix;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(archive/v['copy'],out)
 selected[str(out.relative_to(dest))]={k:v[k] for k in ('bytes','sha256')}
for n in ['VALIDATION.json','FACTORED_MEASUREMENTS.v1.json']:
 shutil.copyfile(archive/n,dest/n);selected[n]=pin((dest/n).read_bytes())
summary=dict(source_commit=head,source_base=r['source_base'],all_original_artifacts_rehashed=len(r['artifacts']),original_artifact_bytes=sum(v['bytes'] for v in r['artifacts'].values()),git_and_snapshot_inputs_verified=len(s['source_inputs']),native_build_runtime_inputs_verified=len(native),all_local_artifacts_fresh_false=True,fresh_local_targets=len(local),host_executable=host['executable_pin'],actual_unique_tests=actual,runtime_groups=16,all_caps_cleanup_pass=True,stages=r['stages'],whole_matched_outputs_preserved=True,source_arrangement_sensitivity_changed_in_logits=True,all_six_gap_fibre=[0,2,3],mechanical_controls_only=True,useful_reconstruction_or_heldout_claim=False,scientific_job=False,GPU_runtime=False,unchanged_Lean_not_recompiled=True,selected_preserved_artifacts=selected)
(dest/'ACCEPTANCE_JOIN.v1.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['stages','actual_unique_tests','selected_preserved_artifacts']},indent=2))
print('compact receipts',len(selected),'bytes',sum(v['bytes'] for v in selected.values()))
