"""Run a command; print its exit status, wall seconds and peak resident set (KiB) on stderr."""
import resource, subprocess, sys, time
t = time.monotonic()
rc = subprocess.call(sys.argv[2:])
print(f"MEASURE lap={sys.argv[1]} rc={rc} wall_s={time.monotonic() - t:.1f} peak_rss_kib={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}", flush=True)
sys.exit(rc)
