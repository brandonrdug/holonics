# Exterior: the tower's guess at the held-out sums' units split into the ring's part (W φ) and the
# rest (the same tower with the ring's readout at zero), from the SPLIT and AT lines of
# read-tower-at ... split, by the operands' lengths. Per group: sums, the whole guess right, the
# ring's part right, the rest right, the code in bits a digit, and the ring's part's margin at the
# arriving class over the largest other (median, on 2^-16 of a bit, so 65536 is one bit).
import sys, collections
text = open(sys.argv[1], "rb").read()
for path in sys.argv[2:]:
    code = {}
    g = collections.defaultdict(lambda: [0, 0, 0, 0, 0, []])
    for line in open(path):
        f = line.split()
        if f and f[0] == "AT": code[int(f[1])] = int(f[4])
        if not f or f[0] != "SPLIT": continue
        i, nxt, top, rt, st = (int(x) for x in f[1:6]); margin = int(f[9])
        s = text.rfind(b"\n", 0, i + 1) + 1
        a, b = text[s:text.find(b"=", s)].split(b"+")
        for k in ("%d+%d" % (len(a), len(b)), "all"):
            v = g[k]; v[0] += 1; v[1] += top == nxt; v[2] += rt == nxt; v[3] += st == nxt; v[4] += code[i]; v[5].append(margin)
    print(path)
    for k in sorted(g, key=lambda k: (k == "all", k)):
        v = g[k]; m = sorted(v[5])
        print("  %s: %d sums; whole %d, ring's part %d, rest %d; %.3f bits a digit; ring's margin median %.2f bits" % (k, v[0], v[1], v[2], v[3], v[4] / 2**20 / v[0], m[len(m) // 2] / 65536))
