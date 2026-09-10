"""Exterior exact incidence witness for the orientation plates; no native execution.

The mesh uses integer vertex addresses. Trigonometry belongs only to its Typst
embedding. A disk with alternating ribbon attachments gives an annulus, a
Mobius band, or Mobius shorts; orientation is solved from actual shared edges.
"""
from collections import defaultdict, deque
from pathlib import Path
import json

PORTS = 4  # the existing tetrahedral chart; this sets only mesh resolution
N = 2 ** PORTS
L = 2 * N
WIDTH = 4
GRID = [-6, -4, -2, -1, 0, 1, 2, 4, 6]  # coordinates / 6


def mesh(twist, second):
    tags = [["disk", i, j] for j in range(9) for i in range(9)]
    faces = []
    def quad(a, b, c, d):
        faces.extend([(a, b, c), (a, c, d)])
    for j in range(8):
        for i in range(8):
            quad(9*j+i, 9*j+i+1, 9*(j+1)+i+1, 9*(j+1)+i)
    for band in range(1 + second):
        rows = []
        for i in range(L+1):
            row = []
            for j in range(WIDTH+1):
                if i in (0, L):
                    if band == 0:
                        y = 2+j if i == 0 or not twist else 6-j
                        vertex = 9*y + (0 if i == 0 else 8)
                    else:
                        vertex = 2+j + (0 if i == 0 else 72)
                else:
                    vertex = len(tags)
                    tags.append(["a" if band == 0 else "b", i, j])
                row.append(vertex)
            rows.append(row)
        for i in range(L):
            for j in range(WIDTH):
                quad(rows[i][j], rows[i+1][j], rows[i+1][j+1], rows[i][j+1])
    return tags, faces


def inspect(faces):
    edges = defaultdict(list)
    vertices = set()
    for f, triangle in enumerate(faces):
        assert len(set(triangle)) == 3
        vertices.update(triangle)
        boundary = defaultdict(int)
        for a, b in zip(triangle, triangle[1:] + triangle[:1]):
            edge = tuple(sorted((a, b)))
            sign = 1 if (a, b) == edge else -1
            edges[edge].append((f, sign))
            boundary[a] -= 1
            boundary[b] += 1
        assert not any(boundary.values())  # boundary squared = 0
    assert all(len(adj) in (1, 2) for adj in edges.values())
    neighbors = defaultdict(list)
    bdry = defaultdict(list)
    for (a, b), adj in edges.items():
        if len(adj) == 1:
            bdry[a].append(b)
            bdry[b].append(a)
        else:
            (f, sf), (g, sg) = adj
            transition = -sf*sg
            neighbors[f].append((g, transition))
            neighbors[g].append((f, transition))
    assert all(len(ns) == 2 for ns in bdry.values())
    unseen = set(bdry)
    loops = []
    while unseen:
        start = min(unseen)
        loop = [start]
        prev, at = None, start
        while True:
            nxt = next(v for v in bdry[at] if v != prev)
            if nxt == start:
                break
            loop.append(nxt)
            prev, at = at, nxt
        unseen.difference_update(loop)
        loops.append(loop)
    signs, parents, conflict = {}, {}, None
    components = 0
    for root in range(len(faces)):
        if root in signs:
            continue
        components += 1
        signs[root] = 1
        parents[root] = None
        queue = deque([root])
        while queue:
            f = queue.popleft()
            for g, t in neighbors[f]:
                if g not in signs:
                    signs[g], parents[g] = t*signs[f], f
                    queue.append(g)
                elif signs[g] != t*signs[f] and conflict is None:
                    def ancestry(v):
                        path = []
                        while v is not None:
                            path.append(v)
                            v = parents[v]
                        return path
                    pf, pg = ancestry(f), ancestry(g)
                    join = next(v for v in pf if v in pg)
                    conflict = pf[:pf.index(join)+1] + list(reversed(pg[:pg.index(join)])) + [f]
    if conflict:
        product = 1
        for f, g in zip(conflict, conflict[1:]):
            product *= next(t for h, t in neighbors[f] if h == g)
        assert product == -1
    # A genuine surface also requires each vertex link to be a circle or interval.
    for v in vertices:
        link = defaultdict(set)
        for face in faces:
            if v in face:
                a, b = [w for w in face if w != v]
                link[a].add(b)
                link[b].add(a)
        reached, todo = set(), [next(iter(link))]
        while todo:
            at = todo.pop()
            if at not in reached:
                reached.add(at)
                todo.extend(link[at] - reached)
        assert reached == set(link)
        ends = sum(len(adj) == 1 for adj in link.values())
        assert ends == (2 if v in bdry else 0)
        assert all(len(adj) in (1, 2) for adj in link.values())
    return dict(V=len(vertices), E=len(edges), F=len(faces),
                chi=len(vertices)-len(edges)+len(faces), boundary_count=len(loops),
                orientable=conflict is None, components=components,
                boundary_loops=loops, reversing_loop=conflict), edges


def orientation_cover(faces, edges):
    parent = list(range(6*len(faces)))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x, y):
        parent[find(x)] = find(y)
    def corner(f, sheet, v):
        return 6*f + 3*sheet + faces[f].index(v)
    for edge, adj in edges.items():
        if len(adj) == 2:
            (f, sf), (g, sg) = adj
            for sheet in (0, 1):
                target = sheet if -sf*sg == 1 else 1-sheet
                for v in edge:
                    union(corner(f, sheet, v), corner(g, target, v))
    lifted = []
    for f, face in enumerate(faces):
        for sheet in (0, 1):
            lifted.append(tuple(find(corner(f, sheet, v)) for v in
                                (face if sheet == 0 else tuple(reversed(face)))))
    result, _ = inspect(lifted)
    assert result["orientable"]
    roots = sorted({v for face in lifted for v in face})
    lookup = {v: i for i, v in enumerate(roots)}
    base_vertices = {}
    for f, face in enumerate(faces):
        for sheet in (0, 1):
            for v in face:
                root = find(corner(f, sheet, v))
                assert root not in base_vertices or base_vertices[root] == v
                base_vertices[root] = v
    shell = list(lifted)
    for (a, b), adj in edges.items():
        if len(adj) == 1:
            f = adj[0][0]
            a0, b0, a1, b1 = [find(corner(f, sheet, v)) for sheet, v in
                              ((0, a), (0, b), (1, a), (1, b))]
            shell.extend([(a0, b0, b1), (a0, b1, a1)])
    shell_result, _ = inspect(shell)
    assert shell_result["orientable"] and shell_result["boundary_count"] == 0
    assert shell_result["components"] == 1
    assert shell_result["chi"] == result["chi"]
    geometry = dict(base_vertices=[base_vertices[v] for v in roots],
                    faces=[tuple(lookup[v] for v in face) for face in lifted],
                    rim=[tuple(lookup[v] for v in face) for face in shell[len(lifted):]])
    fibres = defaultdict(list)
    for v, base in enumerate(geometry["base_vertices"]):
        fibres[base].append(v)
    assert all(len(pair) == 2 for pair in fibres.values())
    deck = [None] * len(roots)
    for a, b in fibres.values():
        deck[a], deck[b] = b, a
    cover_edges = {tuple(sorted((a, b))) for face in geometry["faces"]
                   for a, b in zip(face, face[1:]+face[:1])}
    assert {tuple(sorted((deck[a], deck[b]))) for a, b in cover_edges} == cover_edges
    adjacency = [set() for _ in roots]
    for a, b in cover_edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    # Thus the unit vertex Laplacian commutes with the deck permutation on
    # every basis vector; heat preserves both even scalars and odd coefficients.
    for v in range(len(roots)):
        assert {deck[w] for w in adjacency[v]} == adjacency[deck[v]]
    geometry["deck"] = deck
    geometry["laplacian_deck_commutes"] = True
    geometry["vertex_heat_step"] = [1, 2*max(map(len, adjacency))]
    return result, shell_result, geometry


def mv(a, v):
    return tuple(sum(x*y for x, y in zip(row, v)) for row in a)


def main():
    out = dict(N=N, L=L, width=WIDTH, grid=GRID, surfaces={})
    for name, twist, second, expected in (
        ("annulus", False, False, (0, 2, True, 2)),
        ("mobius", True, False, (0, 1, False, 1)),
        ("shorts", True, True, (-1, 1, False, 1)),
    ):
        tags, faces = mesh(twist, second)
        result, edges = inspect(faces)
        cover, shell, cover_mesh = orientation_cover(faces, edges)
        assert (result["chi"], result["boundary_count"], result["orientable"],
                cover["components"]) == expected
        assert cover["chi"] == 2*result["chi"]
        assert cover["boundary_count"] == 2*result["boundary_count"]
        out["surfaces"][name] = dict(tags=tags, faces=faces, topology=result,
                                     cover=cover, shell=shell, cover_mesh=cover_mesh)
    a, b, x = ((1, 0), (0, -1)), ((0, -1), (1, 0)), (1, 2)
    ba, ab = mv(b, mv(a, x)), mv(a, mv(b, x))
    assert ba == (2, 1) and ab == (-2, -1)
    assert tuple(u-v for u, v in zip(ba, ab)) == (4, 2)
    assert sum(v*v for v in ba) == sum(v*v for v in ab) == 5
    out["connection"] = dict(A=a, B=b, x=x, BAx=ba, ABx=ab, difference=(4, 2))
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, separators=(",", ":"))+"\n")
    for name, surface in out["surfaces"].items():
        t, c, shell = surface["topology"], surface["cover"], surface["shell"]
        print(f"{name}: chi={t['chi']}, boundaries={t['boundary_count']}, "
              f"orientable={t['orientable']}; cover chi={c['chi']}, "
              f"boundaries={c['boundary_count']}, components={c['components']}; "
              f"closed orientable shell genus={(2-shell['chi'])//2}")
    print("Returned: surface links; boundary squared; reversing loop products; "
          "orientation covers and deck-equivariant diffusion; exact order-sensitive transport.")


if __name__ == "__main__":
    main()
