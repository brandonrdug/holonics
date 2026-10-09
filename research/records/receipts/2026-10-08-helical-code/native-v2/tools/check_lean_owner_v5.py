"""Exact compiler read; raw diagnostics reach files even if its deadline stops it."""
from pathlib import Path
import importlib.util, json, re, subprocess, sys, time
desc=json.loads(Path(sys.argv[1]).read_text())
verified=subprocess.run(['/usr/bin/python3.14','-B',desc['metadata_verifier'],sys.argv[1],'precompile'])
assert verified.returncode==0,'precompile metadata refused'
p=time.monotonic_ns()
with Path(desc['compiler_stdout']).open('xb') as out, Path(desc['compiler_stderr']).open('xb') as err:
    completed=subprocess.run(desc['compiler_argv'],stdout=out,stderr=err)
wall=time.monotonic_ns()-p
stdout=Path(desc['compiler_stdout']).read_bytes();stderr=Path(desc['compiler_stderr']).read_bytes()
sys.stdout.buffer.write(stdout);sys.stdout.buffer.flush()
sys.stderr.buffer.write(stderr);sys.stderr.buffer.flush()
print(json.dumps({'phase':'Lean compiler','wall_ns':wall,'exit':completed.returncode}),flush=True)
verified=subprocess.run(['/usr/bin/python3.14','-B',desc['metadata_verifier'],sys.argv[1],'postcompile'])
assert verified.returncode==0,'postcompile metadata refused'
reports=list(re.finditer(r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]|^'(.+)' does not depend on any axioms",stdout.decode('utf8',errors='replace'),re.M))
queries=[(x.group(1) or x.group(3),x.group(2) or '') for x in reports]
axioms={name:[a.strip() for a in value.split(',') if a.strip()] for name,value in queries}
expected=desc['expected_selectors'];allowed={'propext','Classical.choice','Quot.sound'}
matches=len(queries)==len(expected) and all(n==x or n.endswith('.'+x) for (n,_),x in zip(queries,expected))
standard=all(set(v)<=allowed for v in axioms.values())
accepted=completed.returncode==0 and matches and standard and b'sorryAx' not in stdout
result={'kernel_accepted':accepted,'compiler_exit':completed.returncode,'compiler_wall_ns':wall,
        'axioms':axioms,'selector_count_matches':matches,'standard_axioms_only':standard,
        'metadata_unchanged':verified.returncode==0,'broad_library_checked':False}
with Path(desc['kernel_receipt']).open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result),flush=True)
sys.exit(0 if accepted else completed.returncode or 1)
