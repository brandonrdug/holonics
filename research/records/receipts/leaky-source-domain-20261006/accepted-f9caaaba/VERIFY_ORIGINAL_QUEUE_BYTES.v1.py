from pathlib import Path
import hashlib,json,subprocess,re
root=Path.cwd();p=root/'research/records/receipts/leaky-source-domain-20261006/native-validation-f9caaaba';j=json.loads((p/'VALIDATION.json').read_text());head=j['source_commit']
def pin(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
for name,want in j['preserved_files'].items():assert pin((p/name).read_bytes())==want,name
snapshot=json.loads((p/'candidate/SOURCE_SNAPSHOT.v1.json').read_text());source_root=Path(snapshot['source_root']);native={n:v for n,v in snapshot['source_inputs'].items() if not n.startswith('lean/')}
for name,want in snapshot['source_inputs'].items():
 assert pin(subprocess.check_output(['git','show',head+':'+name]))==want,name
 assert pin((source_root/name).read_bytes())==want,name
build=json.loads((p/'stages/hnn-material-f9caaaba-host-cuda-link-20261006-v1.input_seal.json').read_text())
for name,want in native.items():assert build['inputs'][str(source_root/name)]==want,name
binding=json.loads((p/'candidate/COMPILE_SOURCE_BINDING.v1.json').read_text());exe=next(q for q in (p/'executables').iterdir() if q.name.startswith('holonics-'));assert pin(exe.read_bytes())==binding['new_holonics_executable_pin']
artifacts=json.loads((p/'candidate/COMPILED_ARTIFACTS.v1.json').read_text())['artifacts'];assert artifacts and all(a['fresh'] is False for a in artifacts)
cargo=[json.loads(line) for line in (p/'stages/hnn-material-f9caaaba-host-cuda-link-20261006-v1.stdout').read_text().splitlines() if line.startswith('{')];local=[a for a in cargo if a.get('reason')=='compiler-artifact' and 'path+file://' in a.get('package_id','')]
assert [{k:v for k,v in a.items() if k!='executable_pin'} for a in artifacts]==local
for artifact in artifacts:
 if artifact.get('executable'):
  assert pin((p/'executables'/Path(artifact['executable']).name).read_bytes())==artifact['executable_pin'],artifact['target']['name']
selected=[];runtime_bindings=[];request_path=root/'.local/material-learning-followup-01a1030c-20261006/COHERENT_FOLLOWUP_CANDIDATE.v6.json';request=json.loads(request_path.read_text());assert pin(request_path.read_bytes())==snapshot['owner_request_pin']
for group,wantgroup in zip(j['runtime_groups'],request['runtime_groups']):
 label=group['label'];raw=(p/f'stages/{label}.stdout').read_text();found=re.findall(r'^test (\S+) \.\.\.',raw,re.M)
 assert len(found)==group['expected_tests']==wantgroup['expected_tests'] and sorted(found)==sorted(group['actual_test_names']),(label,found)
 assert re.search(r'test result: ok\. '+str(len(found))+r' passed; 0 failed; 0 ignored;',raw),label
 inputs=json.loads((p/f'stages/{label}.input_seal.json').read_text())['inputs']
 for name,want in native.items():assert inputs[str(source_root/name)]==want,(label,name)
 executable_inputs=[(name,value) for name,value in inputs.items() if '/cache-v2/debug/deps/' in name and Path(name).name.startswith(('holonics-','ranged_capacity-','source_entrance-')) and not name.endswith('.d')]
 assert len(executable_inputs)==1,(label,executable_inputs)
 name,want=executable_inputs[0];assert pin((p/'executables'/Path(name).name).read_bytes())==want
 selected+=found;runtime_bindings.append({'label':label,'executable':Path(name).name,'pin':want,'native_source_inputs_bound':len(native)})
assert len(selected)==len(set(selected))==18 and set(selected)==set(request['source_only_selector_closure']['exact_selected_names'])
for m in j['measurements']:
 assert m['wall_ns']<=m['fixed_deadline_ns'] and m['aggregate_CPU_ns']<=m['aggregate_CPU_limit_us']*1000
 assert m['group_peak_bytes']<=m['group_memory_max_bytes'] and m['quiescent_release'] is True
summary={'source_commit':head,'all_preserved_artifact_entries_rehashed':len(j['preserved_files']),'preserved_artifact_bytes':sum(v['bytes'] for v in j['preserved_files'].values()),'immutable_git_source_inputs_verified':len(snapshot['source_inputs']),'native_build_runtime_source_inputs_verified':len(native),'unchanged_Lean_leaf_verified_without_runtime_or_compile':True,'actual_unique_native_controls':len(selected),'runtime_executable_bindings':runtime_bindings,'all_local_compiler_artifacts_fresh_false':True,'prediction_example_compiled':any(a['target']['name']=='hnn_prediction' for a in artifacts),'host_CUDA_linked':any(a['target']['name']=='holonics_cuda' for a in artifacts),'GPU_runtime':False,'scientific_job':False,'all_resource_caps_and_cleanup_pass':True,'validation_file':pin((p/'VALIDATION.json').read_bytes()),'behavioral_output_read_from_raw_fixture':True}
q=root/'.local/material-learning-followup-01a1030c-20261006/ACCEPTANCE_REHASH.f9caaaba.v1.json';assert not q.exists();q.write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='runtime_executable_bindings'},indent=2))
