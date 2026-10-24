"""The binding a pair contact carries: the four-cycle (mixed second difference) of each result face.

For a face G(a, b) of a two-operand operation, the four-cycle on the rectangle {i,k} x {j,l} is
G(i,j) - G(i,l) - G(k,j) + G(k,l). It vanishes on every rectangle iff G = f(a) + g(b): the face is
then read from the two operands' own faces (marginals) and composed by one crossing. A nonzero
four-cycle is the binding that neither marginal shows; a pair contact must carry it. Every rectangle
is a sum of unit squares, so unit squares decide.

Charts: a ring face is read as its phase G = value/q in Q/Z (four-cycle taken mod 1); the size is
read as an integer (number of digits); the index chart reads the units of Z/q through a primitive
root. Operands 0..99 (two-digit), base 10. Exact rational arithmetic; no floats.
"""
from fractions import Fraction as Fr
import json, math

N = 100
B = 10

def ndig(n):
    return len(str(n)) if n > 0 else 0

def unit_squares(G, mod1):
    vals = []
    for a in range(N - 1):
        for b in range(N - 1):
            d = G(a, b) - G(a, b + 1) - G(a + 1, b) + G(a + 1, b + 1)
            if mod1:
                d = d - math.floor(d)
            vals.append(((a, b), d))
    return vals

def summary(vals):
    nz = [(p, d) for p, d in vals if d != 0]
    dist = sorted({str(d) for _, d in nz})
    return {"squares": len(vals), "nonzero": len(nz), "values": dist[:6]}

out = {}

# Sum: ring faces are characters of a + b, so their four-cycle is zero.
for q in (10, 9, 11):
    out[f"sum ring {q}"] = summary(unit_squares(lambda a, b, q=q: Fr((a + b) % q, q), True))

# Sum's tens digit, read as a phase on ring 10: its four-cycle sits where a square straddles a
# carry line a + b = 10m (the additive caustic of the units).
v = unit_squares(lambda a, b: Fr(((a + b) // B) % B, B), True)
s = summary(v)
nz = [p for p, d in v if d != 0]
s["all straddle a + b = 10m"] = all(
    any((a + da + b + db) % B == 0 for da in (0, 1) for db in (0, 1)) and
    not all((a + da + b + db) % B == 0 for da in (0, 1) for db in (0, 1))
    for a, b in nz)
# the same binding at digit grain: the carry out of the units digits
carry = [[1 if x + y >= B else 0 for y in range(B)] for x in range(B)]
cnz = [(x, y) for x in range(B - 1) for y in range(B - 1)
       if carry[x][y] - carry[x][y + 1] - carry[x + 1][y] + carry[x + 1][y + 1] != 0]
s["units-carry nonzero squares (digits 0..9)"] = len(cnz)
s["units-carry squares on x + y + 1 = 9 or 10"] = all(x + y + 1 in (B - 1, B) for x, y in cnz)
out["sum tens digit"] = s

# Product on a ring, additive phase chart: the four-cycle of ab/q is (i-k)(j-l)/q, so every unit
# square carries the same 1/q: the pairing of the ring.
for q in (10, 9, 11, 101):
    out[f"product ring {q} (phase ab/q)"] = summary(unit_squares(lambda a, b, q=q: Fr(a * b % q, q), True))

# Product on the units of Z/q, index chart: dlog(ab) = dlog a + dlog b, so the four-cycle vanishes
# on every rectangle of units; the binding is left only on operands sharing a prime with q.
def index_chart(q, g):
    idx, x = {}, 1
    order = 0
    while True:
        idx[x] = order
        order += 1
        x = x * g % q
        if x == 1:
            break
    return idx, order

for q, g in ((9, 2), (11, 2), (10, 3), (101, 2)):
    idx, order = index_chart(q, g)
    units = sorted(idx)
    assert len(units) == sum(1 for u in range(1, q) if math.gcd(u, q) == 1)
    G = lambda a, b: Fr(idx[a * b % q], order)
    # G is separable iff every rectangle anchored at (1, 1) vanishes: any rectangle's four-cycle is
    # a signed sum of four anchored ones.
    rect = nonzero = 0
    for i in units[1:]:
        for j in units[1:]:
            d = G(i, j) - G(i, 1) - G(1, j) + G(1, 1)
            d -= math.floor(d)
            rect += 1
            nonzero += d != 0
    out[f"product units of Z/{q} (index chart, root {g})"] = {"anchored rectangles": rect, "nonzero": nonzero, "units": len(units), "order": order}

# Product size, integer chart: number of digits of ab. Its four-cycle sits only where a square
# straddles a hyperbola ab = 10^k (the multiplicative caustic: the leading carry).
v = unit_squares(lambda a, b: ndig(a * b), False)
s = summary(v)
nz = [p for p, d in v if d != 0]
def straddles(a, b):
    lens = {ndig((a + da) * (b + db)) for da in (0, 1) for db in (0, 1)}
    return len(lens) > 1
s["all straddle ab = 10^k"] = all(straddles(a, b) for a, b in nz)
s["squares straddling ab = 10^k"] = sum(1 for a in range(N - 1) for b in range(N - 1) if straddles(a, b))
out["product size (digits of ab)"] = s

print(json.dumps(out, indent=1))
