"""Run a command; print its wall time and the child's peak resident set (bytes)."""
import resource
import subprocess
import sys
import time

t0 = time.time()
res = subprocess.run(sys.argv[1:], capture_output=True, text=True)
wall = time.time() - t0
peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024
print(res.stdout.strip())
print(res.stderr.strip()[-500:])
print(f'exit {res.returncode}; wall {int(wall * 1000)} ms; peak resident {peak} bytes')
