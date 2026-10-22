"""Exterior capture of synthetic class-input control stdout; no model/file IO in machinery.
Usage: python3 tools/capture_class_input_receipt.py CONTROL_LOG NEW_DIRECTORY
"""
import hashlib,json,sys
from pathlib import Path

log=Path(sys.argv[1]);target=Path(sys.argv[2]);raw=log.read_bytes();text=raw.decode()
markers=[line.split('CLASS_INPUT_JSON ',1)[1] for line in text.splitlines() if 'CLASS_INPUT_JSON ' in line]
assert len(markers)==1,'one actual synthetic fixture trace'
receipt=json.loads(markers[0]);assert receipt['kind']=='synthetic_CODE_class_input_preparation'
assert receipt['warm_cold_exact'] and receipt['actual_unchanged_by_prospect']
assert receipt['direct_adjoint_calls']==0 and receipt['actual_arrivals']==4
assert receipt['learned_logits']!=receipt['frozen_logits']
assert text.count('CLASS_INPUT_STATE_BEGIN\n')==text.count('\nCLASS_INPUT_STATE_END')==1
state=text.split('CLASS_INPUT_STATE_BEGIN\n',1)[1].split('\nCLASS_INPUT_STATE_END',1)[0]
assert state.startswith('class-input-v1\n')
assert 'test result: ok. 3 passed' in text
assert 'CLASS_INPUT_COLD_CONTINUATION next_actual_accepted_once=true complete_native_material_exact=true' in text
assert not target.exists();target.mkdir()
(target/'INSPECTABLE_CLASS_INPUT.json').write_text(json.dumps(receipt,indent=2)+'\n')
(target/'COMBINED_CLASS_NATIVE.state').write_text(state)
manifest={'kind':'synthetic_CODE_not_language','log_sha256':hashlib.sha256(raw).hexdigest(),'state_sha256':hashlib.sha256(state.encode()).hexdigest(),'source_control_log':str(log),'model_jobs':0,'claims':'class material/native preparation/readout influence; full native+new material cold without World','limits':'two-symbol chart, authored nonzero R, no selected-law language command, no class CUDA parity, no predictive gain/speedup'}
(target/'DELIVERY_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest))
