"""The six closing orders on a leaking store (host arithmetic; no state of the machine is read).

A store Q <- gamma Q + b holds three arrivals as b_last + gamma b_mid + gamma^2 b_first. Three classes without their
common mode stand at thirds of a turn in a plane. The six orders are then the corners of a hexagon whose sides
alternate: two orders that share their last closer are (gamma - gamma^2)|p - q| apart, two that share their first
(1 - gamma)|p - q|. Printed: the angular gaps around the plane by gamma, and the same at a multiplier that is a turn
by a third, where the holding of an order is one component of the word's transform.
"""
import cmath, itertools, math
u = [cmath.exp(2j * math.pi * k / 3) for k in range(3)]
def corners(gamma):
    pts = {}
    for order in itertools.permutations(range(3)):      # order[0] closes first, order[2] last
        pts[order] = u[order[2]] + gamma * u[order[1]] + gamma ** 2 * u[order[0]]
    return pts
def gaps(pts):
    ang = sorted((math.degrees(cmath.phase(z)) % 360, o) for o, z in pts.items())
    out = []
    for i in range(6):
        a0, o0 = ang[i]; a1, o1 = ang[(i + 1) % 6]
        out.append(((a1 - a0) % 360, o0[2] == o1[2]))
    return out
for g in (0.1, 0.3, 0.5, 0.8, 0.95):
    gs = gaps(corners(g))
    short = [round(x, 1) for x, same in gs if same]; long_ = [round(x, 1) for x, same in gs if not same]
    r = abs(corners(g)[(0, 1, 2)])
    print(f"FORK gamma={g:.2f} gaps between orders sharing their last closer {short}, between the others {long_}, radius {r:.3f}")
# the read's centroids (the lead's fork.txt, unpumped): short sides 10, 40, 58 against long 71, 90, 90
def half_short(g):
    z = corners(g)[(0, 1, 2)] * cmath.exp(-2j * math.pi * 2 / 3)
    return abs(math.degrees(cmath.phase(z)))
for target in (10, 40, 58):
    lo, hi = 0.0, 0.999
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if 2 * half_short(mid) < target else (lo, mid)
    print(f"FORK a short side of {target} degrees is gamma={lo:.2f} at classes a third of a turn apart")
# a turn by a third: weights the cube roots of unity
w = cmath.exp(2j * math.pi / 3)
import random
random.seed(7)
a, b, c = u
Z = {o: [a, b, c][o[2]] + w * [a, b, c][o[1]] + w * w * [a, b, c][o[0]] for o in itertools.permutations(range(3))}
def parity(o):
    return sum(1 for i in range(3) for j in range(i + 1, 3) if o[i] > o[j]) % 2
print("FORK turn by a third, classes at thirds: " + " ".join(f"{o}:p{parity(o)}:|Z|={abs(z):.3f}" for o, z in sorted(Z.items())))
# classes in general position in 5 real dimensions, the multiplier a turn by a third in each of 5 complex circles
vs = [[random.gauss(0, 1) for _ in range(5)] for _ in range(3)]
m = [sum(v[i] for v in vs) / 3 for i in range(5)]
vs = [[v[i] - m[i] for i in range(5)] for v in vs]
H = {o: [vs[o[2]][i] + w * vs[o[1]][i] + w * w * vs[o[0]][i] for i in range(5)] for o in itertools.permutations(range(3))}
ref = H[(0, 1, 2)]
def rel(o):
    num = sum(x * y.conjugate() for x, y in zip(H[o], ref)); den = sum(abs(y) ** 2 for y in ref)
    return num / den
print("FORK turn by a third, classes in general position: holding against the order (0,1,2): " + " ".join(f"{o}:p{parity(o)}:{abs(rel(o)):.3f}@{math.degrees(cmath.phase(rel(o))) % 360:.0f}" for o in sorted(H)))
