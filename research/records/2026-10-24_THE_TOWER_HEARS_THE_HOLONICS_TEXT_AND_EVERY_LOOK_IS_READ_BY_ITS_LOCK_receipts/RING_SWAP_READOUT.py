# Exterior diagnosis: swap the ring's readout W between two learners of one layout, by the material
# entries in which the founded learner differs from the joined one (W opens at zero at the join, and
# the founding moves only W). Rows that are zero in both (classes the founding passage never met)
# lie outside the swapped span and stay as they were. usage (from .local/run):
#   python3 -I RING_SWAP_READOUT.py JOINED FOUNDED PASSED OUT_PASSED_TOWER_FOUNDED_W OUT_FOUNDED_TOWER_PASSED_W
import sys


def load(path):
    return open(path).read().split("\n")


joined, founded, passed = (load(p) for p in sys.argv[1:4])
tj, tf, tp = (x[1].split(" ") for x in (joined, founded, passed))
moved = [i for i, (a, b) in enumerate(zip(tj, tf)) if a != b]
lo, hi = moved[0], moved[-1] + 1
print("readout entries moved by the founding", len(moved), "span", lo, hi)


def rms(v):
    return (sum(int(x) ** 2 for x in v) / len(v)) ** 0.5


print("readout rms founded", round(rms(tf[lo:hi])), "passed", round(rms(tp[lo:hi])), "on 2^-24")


def write(path, base, source):
    material = base[1].split(" ")
    material[lo:hi] = source[1].split(" ")[lo:hi]
    out = list(base)
    out[1] = " ".join(material)
    open(path, "x").write("\n".join(out))


write(sys.argv[4], passed, founded)
write(sys.argv[5], founded, passed)
