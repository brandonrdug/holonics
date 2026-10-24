# The carry as a heat bath: exact checks of the carries chain (Holte 1997; Diaconis-Fulman 2009) and of
# carry lookahead (generate, propagate, kill), and the carries of the passage's sums.
# usage: python3 -I carries.py PASSAGE OUT_JSON
from fractions import Fraction
from math import comb, factorial
import itertools, json, re, sys
def chain(n, b):
    P = [[Fraction(0)] * n for _ in range(n)]
    for c in range(n):
        for ds in itertools.product(range(b), repeat=n):
            P[c][(c + sum(ds)) // b] += Fraction(1, b ** n)
    return P
def det(M):
    M = [r[:] for r in M]; n = len(M); d = Fraction(1)
    for i in range(n):
        k = next((r for r in range(i, n) if M[r][i] != 0), None)
        if k is None: return Fraction(0)
        if k != i: M[i], M[k] = M[k], M[i]; d = -d
        d *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            for c in range(i, n): M[r][c] -= f * M[i][c]
    return d
def eulerian(n, j): return sum((-1) ** i * comb(n + 1, i) * (j + 1 - i) ** n for i in range(j + 2))
out = {"chains": []}
for n, b in ((2, 2), (2, 10), (3, 2), (3, 10), (4, 3)):
    P = chain(n, b)
    pi = [Fraction(eulerian(n, j), factorial(n)) for j in range(n)]
    stat = all(sum(pi[i] * P[i][j] for i in range(n)) == pi[j] for j in range(n))
    eig = all(det([[P[i][j] - (Fraction(1, b ** k) if i == j else 0) for j in range(n)] for i in range(n)]) == 0 for k in range(n))
    out["chains"].append({"summands": n, "base": b, "stationary is Eulerian/n!": stat, "eigenvalues 1, 1/b, ..": eig,
                          "stationary": [str(x) for x in pi]})
    print("n=%d b=%d stationary Eulerian %s, eigenvalues 1/b^k %s, pi %s" % (n, b, stat, eig, [str(x) for x in pi]))
# carry lookahead, two summands: the carry into a place is unread after m lower places exactly when all m
# pair sums equal b - 1 (propagate); probability b^-m
for b in (2, 10):
    for m in (1, 2, 3):
        prop = sum(1 for ds in itertools.product(range(b), repeat=2 * m) if all(ds[2 * i] + ds[2 * i + 1] == b - 1 for i in range(m)))
        print("b=%d m=%d: propagate-through share %s = b^-m %s" % (b, m, Fraction(prop, b ** (2 * m)), Fraction(prop, b ** (2 * m)) == Fraction(1, b ** m)))
# the passage's sums x + y: carries by place (units first)
passage = open(sys.argv[1], "rb").read()
by_place = {}; tot = [0, 0]
for mm in re.finditer(rb"<<(\d+)\+(\d+)=(\d+)>>", passage):
    x, y = mm.group(1).decode()[::-1], mm.group(2).decode()[::-1]
    c = 0
    for k in range(max(len(x), len(y))):
        s = (int(x[k]) if k < len(x) else 0) + (int(y[k]) if k < len(y) else 0) + c
        c = s // 10
        if k < len(x) and k < len(y):
            a = by_place.setdefault(min(k, 3), [0, 0]); a[0] += 1; a[1] += c; tot[0] += 1; tot[1] += c
out["passage sums: places with both digits, carries out, by place from the units (3 = 3 and above)"] = by_place
out["passage sums: all"] = tot
print("passage sums, carry out by place (places, carries):", by_place, "all", tot, "share %.3f" % (tot[1] / tot[0]))
json.dump(out, open(sys.argv[2], "w"), indent=1)
