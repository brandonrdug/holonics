# Exterior: the ring's units read (nearest mean direction, cell left out) at B, E (=), H (a
# three-digit result's leading digit) and U, split by the result's length.
import sys, numpy as np
text = open(sys.argv[1], "rb").read()
U = [int(x) for x in open(sys.argv[2]).read().split()]
def rows(p): return {int(l.split()[1]): l.split() for l in open(p) if l.startswith("FORMS")}
R = {k: rows(f) for k, f in zip("BEHU", sys.argv[3:7])}
y, length, cells = [], [], []
for u in U:
    line = text[text.rfind(b"\n", 0, u) + 1:text.find(b"\n", u)].decode()
    lhs, rhs = line.split("=")
    a, b = lhs.split("+")
    e = text.rfind(b"=", 0, u + 1)
    y.append((int(a) + int(b)) % 10); length.append(len(rhs))
    cells.append({"B": e - 1, "E": e, "H": u - 1 if u - 1 > e else None, "U": u})
y = np.array(y); length = np.array(length)
def loo(z, yy):
    right = 0
    for i in range(len(z)):
        best = None
        for c in set(yy):
            m = z[yy == c].sum() - (z[i] if yy[i] == c else 0)
            if abs(m) == 0: continue
            s = (z[i] * np.conj(m)).real / abs(m)
            if best is None or s > best[0]: best = (s, c)
        right += best[1] == yy[i]
    return right
for L in (2, 3):
    sel = np.where(length == L)[0]
    out = []
    for k in "BEHU":
        if k == "H" and L == 2: continue
        z = np.array([complex(float(R[k][cells[i][k]][3]), float(R[k][cells[i][k]][4])) for i in sel])
        z = z / np.abs(z)
        out.append("%s %d" % (k, loo(z, y[sel])))
    print("results of %d digits (%d sums):" % (L, len(sel)), ", ".join(out), "of", len(sel))
la = []; lb = []
for u in U:
    line = text[text.rfind(b"\n", 0, u) + 1:text.find(b"\n", u)].decode()
    a, b = line.split("=")[0].split("+")
    la.append(len(a)); lb.append(len(b))
la = np.array(la); lb = np.array(lb)
zB = np.array([complex(float(R["B"][c["B"]][3]), float(R["B"][c["B"]][4])) for c in cells]); zB /= np.abs(zB)
zU = np.array([complex(float(R["U"][c["U"]][3]), float(R["U"][c["U"]][4])) for c in cells]); zU /= np.abs(zU)
for A in (1, 2):
    for Bl in (1, 2):
        sel = np.where((la == A) & (lb == Bl))[0]
        if len(sel) < 20: print("operands of %d and %d digits: %d sums" % (A, Bl, len(sel))); continue
        print("operands of %d and %d digits (%d sums): B %d, U %d" % (A, Bl, len(sel), loo(zB[sel], y[sel]), loo(zU[sel], y[sel])))
