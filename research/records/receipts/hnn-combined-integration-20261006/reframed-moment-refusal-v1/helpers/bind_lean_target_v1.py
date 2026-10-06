"""Rebind only a corrected target when its accepted imported closure is unchanged."""
from pathlib import Path
import importlib.util, json, sys, time
started=time.monotonic_ns();desc=json.loads(Path(sys.argv[1]).read_text())
spec=importlib.util.spec_from_file_location('accepted_import_sealer',desc['sealer'])
seal=importlib.util.module_from_spec(spec);spec.loader.exec_module(seal)
sealed=json.loads(Path(desc['previous_seal']).read_text())
assert not seal.verify_file_records(sealed['file_records']),'accepted imported closure changed'
source=Path(desc['source']);new=seal.capture_path(source)
assert new['sha256']==desc['expected_source_sha256']
target=next(row for row in sealed['modules'] if row['module']==sealed['target'])
assert seal.parse_imports(source.read_text(),sealed['target'])==target['imports'],'import closure changed'
target['source_path']=str(source);target['source_sha256']=new['sha256']
target['source_lookup_precedence']=[{'path':str(source),'present':True,'selected':True}]
sealed['target_source']=str(source);sealed['file_records'][str(source)]=new
for p in desc['code_inputs']:
    sealed['file_records'][p]=seal.capture_path(p)
assert not seal.verify_file_records(sealed['file_records']),'refreshed target inputs changed'
sealed['target_rebinding']={'previous_seal':desc['previous_seal'],
    'imports_unchanged':True,'old_failed_source_preserved':True,
    'fresh_output_target_absent':all(not Path(p).exists() for p in desc['compiler_outputs'])}
assert sealed['target_rebinding']['fresh_output_target_absent']
with Path(desc['seal_output']).open('x') as f:json.dump(sealed,f,separators=(',',':'));f.write('\n')
receipt={'target':sealed['target'],'complete_import_seal_rebound':True,
    'wall_ns':time.monotonic_ns()-started,'projection_ns':desc['preparation_projection_ns'],
    'new_source_sha256':new['sha256'],'module_count':sealed['module_count'],
    'compiler_launched':False,'imports_unchanged':True}
with Path(desc['preparation_receipt']).open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(json.dumps(receipt),flush=True)
