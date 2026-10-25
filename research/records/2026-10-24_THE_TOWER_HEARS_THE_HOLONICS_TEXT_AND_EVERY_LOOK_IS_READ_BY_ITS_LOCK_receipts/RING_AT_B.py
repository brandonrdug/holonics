# Exterior read: the ring's face at each held-out sum's second-operand cell B, read by nearest mean
# direction with each cell left out, labelled by the sum's units. usage (from .local/run):
#   python3 -I RING_AT_B.py DEV_ARITHMETIC U_CELLS AT_U_FILE AT_B_FILE...
# AT_U_FILE is a `read-tower-at` read at the units cells (its FORMS lines give each cell's class);
# each AT_B_FILE is a `read-tower-at` read at the B cells.
import sys
import numpy as np

text = open(sys.argv[1], "rb").read()
U = [int(x) for x in open(sys.argv[2]).read().split()]
label = {int(l.split()[1]): int(l.split()[2]) for l in open(sys.argv[3]) if l.startswith("FORMS")}
B = []
for u in U:
    j = text.rfind(b"=", 0, u + 1) - 1
    while text[j:j + 1] == b" ":
        j -= 1
    B.append(j)
y = np.array([label[u] for u in U])
for path in sys.argv[4:]:
    rows = {int(l.split()[1]): l.split() for l in open(path) if l.startswith("FORMS")}
    z = np.array([float(rows[b][3]) + 1j * float(rows[b][4]) for b in B])
    unit = z / np.abs(z)
    right = 0
    for i in range(len(y)):
        best = None
        for c in set(y):
            m = unit[y == c].sum() - (unit[i] if y[i] == c else 0)
            s = (unit[i] * np.conj(m)).real / abs(m)
            if best is None or s > best[0]:
                best = (s, c)
        right += best[1] == y[i]
    print(path, "outside read of the sum's units at B:", right, "of", len(y))
