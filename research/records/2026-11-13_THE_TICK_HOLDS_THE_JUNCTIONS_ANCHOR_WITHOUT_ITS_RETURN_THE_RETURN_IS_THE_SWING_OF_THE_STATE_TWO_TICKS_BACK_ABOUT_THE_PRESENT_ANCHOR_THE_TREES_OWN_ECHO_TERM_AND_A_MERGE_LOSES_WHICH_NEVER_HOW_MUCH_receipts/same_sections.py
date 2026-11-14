"""same_sections: a reproduction's STORE_SECTION lines against a line's own lap's, timings aside (a host ruler).
usage: python3 -I same_sections.py REPRO_LOG LINE_LOG
Prints the count read, the count equal, and the first difference."""
import sys
TIMING = ("regions_ms=", "deposit_ms=", "ms=")
def rows(path):
    out = []
    for line in open(path):
        if line.startswith("STORE_SECTION "):
            out.append(" ".join(w for w in line.split() if not w.startswith(TIMING)))
    return out
a, b = rows(sys.argv[1]), rows(sys.argv[2])
n = min(len(a), len(b))
same = sum(1 for x, y in zip(a, b) if x == y)
print(f"SAME_SECTIONS read={len(a)} line={len(b)} compared={n} equal={same}")
for x, y in zip(a, b):
    if x != y:
        print("FIRST_DIFF repro=" + x[:300])
        print("FIRST_DIFF line =" + y[:300])
        break
sys.exit(0 if same == n and n == len(a) and n > 0 else 1)
