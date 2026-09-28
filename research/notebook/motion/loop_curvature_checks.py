"""Exact checks of the loop-curvature record's finite claims (standard library only).

The record: research/records/2026-09-28_A_LOOP_READS_THE_CURVATURE_IT_ENCLOSES_RINGS_TUBES_EGGS_AND_NAVIGATION_BY_REWEIGHTING.md.
- first Betti numbers of two square cell complexes: the cube's surface (a sphere) and a 3 x 4 torus;
- metric dimensions by exhaustive search: grids, prisms C_n x P_2, tori C_m x C_n, the path P_3 and the star K_(1,3);
- the reduced-cost counterexample to choosing the neighbour of least h.
Each line prints the claim and its exact value.
"""
import collections
import itertools
from fractions import Fraction


def rank(rows):
    m = [[Fraction(x) for x in r] for r in rows]
    r = 0
    cols = len(m[0]) if m else 0
    for c in range(cols):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def betti1(vertices, edges, faces):
    vi = {v: i for i, v in enumerate(vertices)}
    ei = {e: i for i, e in enumerate(edges)}
    d1 = [[0] * len(edges) for _ in vertices]
    for j, (a, b) in enumerate(edges):
        d1[vi[b]][j] += 1
        d1[vi[a]][j] -= 1
    d2 = [[0] * len(faces) for _ in edges]
    for k, f in enumerate(faces):
        for a, b in zip(f, f[1:] + f[:1]):
            if (a, b) in ei:
                d2[ei[(a, b)]][k] += 1
            else:
                d2[ei[(b, a)]][k] -= 1
    return len(edges) - rank(d1) - rank(d2)


def torus(m, n):
    V = [(i, j) for i in range(m) for j in range(n)]
    E = [((i, j), ((i + 1) % m, j)) for i, j in V] + [((i, j), (i, (j + 1) % n)) for i, j in V]
    F = [[(i, j), ((i + 1) % m, j), ((i + 1) % m, (j + 1) % n), (i, (j + 1) % n)] for i, j in V]
    return V, E, F


def cube_surface():
    C = [(x, y, z) for x in (0, 1) for y in (0, 1) for z in (0, 1)]
    E = [(a, b) for a in C for b in C if a < b and sum(abs(p - q) for p, q in zip(a, b)) == 1]
    F = []
    for axis in range(3):
        for value in (0, 1):
            face = [v for v in C if v[axis] == value]
            ordered = [face[0]]
            while len(ordered) < 4:
                ordered.append(next(w for w in face if w not in ordered
                                    and sum(abs(p - q) for p, q in zip(w, ordered[-1])) == 1))
            F.append(ordered)
    return C, E, F


def distances(graph, source):
    d = {source: 0}
    queue = collections.deque([source])
    while queue:
        v = queue.popleft()
        for w in graph[v]:
            if w not in d:
                d[w] = d[v] + 1
                queue.append(w)
    return d


def metric_dimension(graph):
    V = list(graph)
    D = {v: distances(graph, v) for v in V}
    for k in range(1, len(V)):
        for S in itertools.combinations(V, k):
            if len({tuple(D[s][v] for s in S) for v in V}) == len(V):
                return k


def cycle(n):
    return {i: [(i + 1) % n, (i - 1) % n] for i in range(n)}


def path(n):
    return {i: [j for j in (i - 1, i + 1) if 0 <= j < n] for i in range(n)}


def product(A, B):
    return {(a, b): [(x, b) for x in A[a]] + [(a, y) for y in B[b]] for a in A for b in B}


if __name__ == "__main__":
    print("b1(cube surface, a sphere) =", betti1(*cube_surface()))
    print("b1(3 x 4 torus) =", betti1(*torus(3, 4)))
    print("metric dimension of P4 x P4 =", metric_dimension(product(path(4), path(4))))
    for n in (5, 6, 7):
        print(f"metric dimension of C{n} x P2 =", metric_dimension(product(cycle(n), path(2))))
    for m, n in ((3, 4), (4, 4), (5, 5)):
        print(f"metric dimension of C{m} x C{n} =", metric_dimension(product(cycle(m), cycle(n))))
    star = {0: [1, 2, 3], 1: [0], 2: [0], 3: [0]}
    print("metric dimension of P3 =", metric_dimension(path(3)), "; of K(1,3) =", metric_dimension(star))
    # reduced costs: edges s->t 9, s->b 1, b->t 1; h is the exact distance to t
    cost = {("s", "t"): 9, ("s", "b"): 1, ("b", "t"): 1}
    h = {"t": 0, "b": 1, "s": 2}
    least_h = min(["t", "b"], key=lambda v: h[v])
    zero_reduced = [v for (u, v), c in cost.items() if u == "s" and c - h[u] + h[v] == 0]
    print("least-h neighbour of s:", least_h, "(cost 9, not optimal); zero-reduced-cost neighbours:", zero_reduced)
