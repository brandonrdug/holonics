"""Exact owner compiler read with accepted metadata pre/post verification.

Resource admission, lease and cleanup remain exclusively in the existing runner.
Raw compiler output is retained and forwarded without a diagnostic filter.
"""
from pathlib import Path
import importlib.util, json, re, subprocess, sys, time
desc = json.loads(Path(sys.argv[1]).read_text())
spec = importlib.util.spec_from_file_location('accepted_import_sealer',desc['sealer'])
seal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(seal)
p=time.monotonic_ns()
sealed=json.loads(Path(desc['import_seal']).read_text())
print(json.dumps({'phase':'sealed JSON read','wall_ns':time.monotonic_ns()-p}),flush=True)
p=time.monotonic_ns()
changed=seal.verify_file_records(sealed['file_records'])
assert not changed, ('precompile metadata changed',changed[:8])
print(json.dumps({'phase':'precompile metadata','wall_ns':time.monotonic_ns()-p}),flush=True)
p=time.monotonic_ns()
completed=subprocess.run(desc['compiler_argv'],capture_output=True)
wall=time.monotonic_ns()-p
Path(desc['compiler_stdout']).write_bytes(completed.stdout)
Path(desc['compiler_stderr']).write_bytes(completed.stderr)
sys.stdout.buffer.write(completed.stdout);sys.stdout.buffer.flush()
sys.stderr.buffer.write(completed.stderr);sys.stderr.buffer.flush()
print(json.dumps({'phase':'Lean compiler','wall_ns':wall,'exit':completed.returncode}),flush=True)
p=time.monotonic_ns()
changed=seal.verify_file_records(sealed['file_records'])
assert not changed, ('postcompile metadata changed',changed[:8])
print(json.dumps({'phase':'postcompile metadata','wall_ns':time.monotonic_ns()-p}),flush=True)
queries=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",completed.stdout.decode('utf8',errors='replace'))
axioms={name:[a.strip() for a in value.split(',') if a.strip()] for name,value in queries}
allowed={'propext','Classical.choice','Quot.sound'}
expected=desc['expected_selectors']
selectors_match=len(axioms)==len(expected) and all(
    any(name==wanted or name.endswith('.'+wanted) for name in axioms) for wanted in expected)
standard=all(set(values)<=allowed for values in axioms.values())
accepted=completed.returncode==0 and selectors_match and standard and b'sorryAx' not in completed.stdout
result={'kernel_accepted':accepted,'compiler_exit':completed.returncode,
        'compiler_wall_ns':wall,'axioms':axioms,'selector_count_matches':selectors_match,
        'standard_axioms_only':standard,'metadata_unchanged':not changed,
        'broad_library_checked':False}
with Path(desc['kernel_receipt']).open('x') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result),flush=True)
sys.exit(0 if accepted else completed.returncode or 1)
