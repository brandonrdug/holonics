# The tower's own top guess at the held-out sums' units (AT lines of read-tower-at), by the
# operands' lengths, and its code there in bits a digit.
import sys, collections
text = open(sys.argv[1], "rb").read()
for path in sys.argv[2:]:
    g = collections.defaultdict(lambda: [0, 0, 0])
    for line in open(path):
        if not line.startswith("AT "): continue
        _, c, nxt, top, code = line.split(); c = int(c)
        s = text.rfind(b"\n", 0, c + 1) + 1
        a, b = text[s:text.find(b"=", s)].split(b"+")
        k = "%d+%d" % (len(a), len(b)); g[k][0] += 1; g[k][1] += nxt == top; g[k][2] += int(code)
    print(path, "; ".join("%s: %d of %d, %.2f bits" % (k, v[1], v[0], v[2] / 2**20 / v[0]) for k, v in sorted(g.items())))
