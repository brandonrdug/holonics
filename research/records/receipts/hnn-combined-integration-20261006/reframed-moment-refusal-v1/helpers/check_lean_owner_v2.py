"""Exact compiler read; raw diagnostics reach files even if its deadline stops it."""
from pathlib import Path
import importlib.util, json, re, subprocess, sys, time
desc=json.loads(Path(sys.argv[1]).read_text())
spec=importlib.util.spec_from_file_location('accepted_import_sealer',desc['sealer'])
seal=importlib.util.module_from_spec(spec);spec.loader.exec_module(seal)
p=time.monotonic_ns();sealed=json.loads(Path(desc['import_seal']).read_text())
print(json.dumps({'phase':'sealed JSON read','wall_ns':time.monotonic_ns()-p}),flush=True)
p=time.monotonic_ns();changed=seal.verify_file_records(sealed['file_records'])
assert not changed,('precompile metadata changed',changed[:8])
print(json.dumps({'phase':'precompile metadata','wall_ns':time.monotonic_ns()-p}),flush=True)
p=time.monotonic_ns()
with Path(desc['compiler_stdout']).open('xb') as out, Path(desc['compiler_stderr']).open('xb') as err:
    completed=subprocess.run(desc['compiler_argv'],stdout=out,stderr=err)
wall=time.monotonic_ns()-p
stdout=Path(desc['compiler_stdout']).read_bytes();stderr=Path(desc['compiler_stderr']).read_bytes()
sys.stdout.buffer.write(stdout);sys.stdout.buffer.flush()
sys.stderr.buffer.write(stderr);sys.stderr.buffer.flush()
print(json.dumps({'phase':'Lean compiler','wall_ns':wall,'exit':completed.returncode}),flush=True)
p=time.monotonic_ns();changed=seal.verify_file_records(sealed['file_records'])
assert not changed,('postcompile metadata changed',changed[:8])
print(json.dumps({'phase':'postcompile metadata','wall_ns':time.monotonic_ns()-p}),flush=True)
queries=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",stdout.decode('utf8',errors='replace'))
axioms={name:[a.strip() for a in value.split(',') if a.strip()] for name,value in queries}
expected=desc['expected_selectors'];allowed={'propext','Classical.choice','Quot.sound'}
matches=len(axioms)==len(expected) and all(any(n==x or n.endswith('.'+x) for n in axioms) for x in expected)
standard=all(set(v)<=allowed for v in axioms.values())
accepted=completed.returncode==0 and matches and standard and b'sorryAx' not in stdout
result={'kernel_accepted':accepted,'compiler_exit':completed.returncode,'compiler_wall_ns':wall,
        'axioms':axioms,'selector_count_matches':matches,'standard_axioms_only':standard,
        'metadata_unchanged':not changed,'broad_library_checked':False}
with Path(desc['kernel_receipt']).open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result),flush=True)
sys.exit(0 if accepted else completed.returncode or 1)
