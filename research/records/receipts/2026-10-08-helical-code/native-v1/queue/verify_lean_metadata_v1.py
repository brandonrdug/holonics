"""One bounded sequential metadata reader; exits before the compiler starts."""
from pathlib import Path
import importlib.util, json, sys, time
desc=json.loads(Path(sys.argv[1]).read_text())
spec=importlib.util.spec_from_file_location('accepted_import_sealer',desc['sealer'])
seal=importlib.util.module_from_spec(spec);spec.loader.exec_module(seal)
p=time.monotonic_ns();sealed=json.loads(Path(desc['import_seal']).read_text())
print(json.dumps({'phase':sys.argv[2]+' sealed JSON read','wall_ns':time.monotonic_ns()-p}),flush=True)
p=time.monotonic_ns();changed=seal.verify_file_records(sealed['file_records'])
assert not changed,(sys.argv[2]+' metadata changed',changed[:8])
print(json.dumps({'phase':sys.argv[2]+' metadata','wall_ns':time.monotonic_ns()-p}),flush=True)
