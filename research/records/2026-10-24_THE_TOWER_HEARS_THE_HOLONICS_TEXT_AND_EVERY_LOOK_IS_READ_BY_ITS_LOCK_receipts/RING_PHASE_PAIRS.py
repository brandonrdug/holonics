# Exterior read: the ring's face at each held-out sum's second-operand cell B and units cell U,
# grouped by the operands' units (a0, b0). Reads each class by nearest mean direction with the cell
# left out, how tightly each pair of operands' units sits at one angle, and how far the pair angles
# at B are from a turn for operand A's digit added to a turn for operand B's (fitted by alternating
# circular means). A float read outside the machine. usage (from .local/run):
#   python3 -I RING_PHASE_PAIRS.py DEV_ARITHMETIC U_CELLS AT_U_FILE AT_B_FILE
import sys
import numpy as np

text = open(sys.argv[1], "rb").read()
U = [int(x) for x in open(sys.argv[2]).read().split()]


def rows(path):
    return {int(l.split()[1]): l.split() for l in open(path) if l.startswith("FORMS")}


RU, RB = rows(sys.argv[3]), rows(sys.argv[4])
recs = []
for u in U:
    line = text[text.rfind(b"\n", 0, u) + 1:text.find(b"\n", u)].decode()
    lhs, rhs = line.split("=")
    A, B = lhs.split("+")
    j = text.rfind(b"=", 0, u + 1) - 1
    zb = complex(float(RB[j][3]), float(RB[j][4]))
    zu = complex(float(RU[u][3]), float(RU[u][4]))
    recs.append((int(A), int(B), zb / abs(zb), zu / abs(zu)))
a0 = np.array([r[0] % 10 for r in recs])
b0 = np.array([r[1] % 10 for r in recs])
y = (a0 + b0) % 10
pair = a0 * 10 + b0
for k, name in ((2, "B"), (3, "U")):
    z = np.array([r[k] for r in recs])
    right = 0
    for i in range(len(z)):
        best = None
        for c in set(y):
            m = z[y == c].sum() - (z[i] if y[i] == c else 0)
            if abs(m) == 0:
                continue
            s = (z[i] * np.conj(m)).real / abs(m)
            if best is None or s > best[0]:
                best = (s, c)
        right += best[1] == y[i]
    tight = [abs(z[pair == p].mean()) for p in set(pair) if (pair == p).sum() >= 3]
    print(name, "units by nearest mean direction:", right, "of", len(y),
          "| median resultant within a pair of operands' units (3 or more sums): %.3f" % np.median(tight))
    print(name, "each units class's resultant:", " ".join("%.2f" % abs(z[y == c].mean()) for c in range(10)))
    print(name, "each units class's mean angle (degrees):", " ".join("%d" % (np.degrees(np.angle(z[y == c].mean())) % 360) for c in range(10)))
z = np.array([r[2] for r in recs])
P = {p: (z[pair == p].mean(), (pair == p).sum()) for p in set(pair)}
ta, tb = np.zeros(10), np.zeros(10)
for _ in range(200):
    for d in range(10):
        s = sum(m * n * np.exp(-1j * tb[p % 10]) for p, (m, n) in P.items() if p // 10 == d)
        if s != 0:
            ta[d] = np.angle(s)
    for d in range(10):
        s = sum(m * n * np.exp(-1j * ta[p // 10]) for p, (m, n) in P.items() if p % 10 == d)
        if s != 0:
            tb[d] = np.angle(s)
res = np.array([np.degrees(np.angle(m * np.exp(-1j * (ta[p // 10] + tb[p % 10])))) for p, (m, n) in P.items()])
print("B: a turn for A's digit plus a turn for B's leaves |degrees| median %.1f, largest %.1f" % (np.median(np.abs(res)), np.max(np.abs(res))))
print("B: A's digits' turns from digit 0 (degrees):", " ".join("%d" % (np.degrees(ta[d] - ta[0]) % 360) for d in range(10)))
print("B: B's digits' turns from digit 0 (degrees):", " ".join("%d" % (np.degrees(tb[d] - tb[0]) % 360) for d in range(10)))
