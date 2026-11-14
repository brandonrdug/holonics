"""Run a command; print its exit status, wall seconds and peak resident set (KiB) on stdout.

usage: python3 -I tools/measure.py NAME COMMAND [ARG ...]   prints `MEASURE lap=NAME rc=… wall_s=… peak_rss_kib=…` and exits with the
command's status. The peak is the largest resident set among the command's waited-for children (`RUSAGE_CHILDREN`). Every run and read
script of the store line calls it (C1's reading of November 14, #603; until then it stood untracked in a worktree's `.local/`).
"""
import resource, subprocess, sys, time
t = time.monotonic()
rc = subprocess.call(sys.argv[2:])
print(f"MEASURE lap={sys.argv[1]} rc={rc} wall_s={time.monotonic() - t:.1f} peak_rss_kib={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}", flush=True)
sys.exit(rc)
