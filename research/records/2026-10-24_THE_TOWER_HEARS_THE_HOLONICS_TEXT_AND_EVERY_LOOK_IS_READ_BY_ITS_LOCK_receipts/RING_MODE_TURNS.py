# Exterior: the move a mode of level 0 makes at each arriving byte, from a full modes reading
# (read-tower-modes ... full): its turn arg(λ_t) in degrees, |λ_t| and the pump's |β_t|, by byte.
import sys, math, collections
text = open(sys.argv[1], "rb").read(); mode = int(sys.argv[3])
by = collections.defaultdict(list)
for line in open(sys.argv[2]):
    if not line.startswith("MODES "): continue
    p = line.split(); m = [int(v) for v in p[4].split("=", 1)[1].split(";")[mode].split(",")]
    by[chr(text[int(p[1])])].append(m[6:10])
for c in sorted(by):
    xs = by[c]; turns = sorted({round(math.degrees(math.atan2(li, lr)), 2) for lr, li, _, _ in xs})
    lam = sum(math.hypot(lr, li) for lr, li, _, _ in xs) / len(xs) / 2**30
    beta = sum(math.hypot(gr, gi) for _, _, gr, gi in xs) / len(xs) / 2**30
    print("%-4r n=%4d turn %s degrees, |λ| %.4f, |β| %.4f" % (c, len(xs), "/".join("%+.2f" % t for t in turns), lam, beta))
