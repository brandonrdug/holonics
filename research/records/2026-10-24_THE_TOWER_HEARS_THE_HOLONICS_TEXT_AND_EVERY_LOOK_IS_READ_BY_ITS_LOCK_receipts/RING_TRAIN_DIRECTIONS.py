# Exterior: the ring's units read at the held-out U cells by nearest mean direction, with the
# class means taken from the training text's U cells (a readout's honest ceiling), beside the
# tower's own guess at the same cells, by the operands' lengths.
import sys, collections, math
def forms(path):
    out = []
    for line in open(path):
        if line.startswith("FORMS "):
            _, c, nxt, re, im = line.split()[:5]; z = complex(int(re), int(im))
            out.append((int(c), int(nxt), z / abs(z) if z else 0))
    return out
train = forms(sys.argv[1]); held = forms(sys.argv[2]); text = open(sys.argv[3], "rb").read()
m = collections.defaultdict(complex)
for _, k, z in train: m[k] += z
print("training class resultants:", " ".join("%.2f" % (abs(m[k]) / sum(1 for _, kk, _ in train if kk == k)) for k in sorted(m)))
g = collections.defaultdict(lambda: [0, 0])
for c, k, z in held:
    best = max(m, key=lambda q: (z * m[q].conjugate()).real / abs(m[q]))
    s = text.rfind(b"\n", 0, c + 1) + 1
    a, b = text[s:text.find(b"=", s)].split(b"+")
    key = "%d+%d" % (len(a), len(b)); g[key][0] += 1; g[key][1] += best == k
print("held-out units by the training means: %d of %d;" % (sum(v[1] for v in g.values()), sum(v[0] for v in g.values())), "; ".join("%s %d of %d" % (k, v[1], v[0]) for k, v in sorted(g.items())))
