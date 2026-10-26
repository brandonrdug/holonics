"""Run a command; print its wall time and peak resident set (the child's ru_maxrss) to stderr."""
import resource, subprocess, sys, time
t = time.monotonic()
code = subprocess.call(sys.argv[1:])
wall = time.monotonic() - t
peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
print(f"MEASURED exit={code} wall_s={wall:.3f} peak_rss_kib={peak}", file=sys.stderr)
sys.exit(code)
