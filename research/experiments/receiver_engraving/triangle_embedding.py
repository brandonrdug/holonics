"""Exact embedding checks for finite rational triangle meshes.

The checker uses ``Fraction`` throughout.  AABB overlap is only a broad phase;
every candidate pair is then tested with exact plane, segment, and coplanar
2-D predicates.  A pair may meet only in the vertices/edge that its face
indices already declare in common.
"""

from collections import defaultdict, deque
from fractions import Fraction as Q

Point = tuple[Q, Q, Q]
Face = tuple[int, int, int]


def qpoint(p) -> Point:
    if any(not isinstance(x, (int, Q)) for x in p):
        raise TypeError("exact geometry requires integer or Fraction coordinates")
    return tuple(Q(x) for x in p)  # type: ignore[return-value]


def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def add(a, b): return tuple(x + y for x, y in zip(a, b))
def scale(a, k): return tuple(k * x for x in a)
def dot(a, b): return sum((x * y for x, y in zip(a, b)), Q(0))
def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def normal(tri): return cross(sub(tri[1], tri[0]), sub(tri[2], tri[0]))
def zero(v): return all(x == 0 for x in v)


def aabb(tri):
    return tuple((min(p[i] for p in tri), max(p[i] for p in tri)) for i in range(3))


def aabb_overlap(a, b):
    return all(x[0] <= y[1] and y[0] <= x[1] for x, y in zip(a, b))


def plane_side(n, origin, p): return dot(n, sub(p, origin))


def point_in_triangle(p, tri):
    n = normal(tri)
    if plane_side(n, tri[0], p) != 0:
        return False
    signs = [dot(cross(sub(tri[(i + 1) % 3], tri[i]), sub(p, tri[i])), n)
             for i in range(3)]
    return all(s >= 0 for s in signs) or all(s <= 0 for s in signs)


def segment_triangle_hit(p, q, tri):
    """Return an exact hit point for a non-coplanar segment/triangle pair."""
    n = normal(tri)
    d = sub(q, p)
    den = dot(n, d)
    if den == 0:
        return None
    t = -plane_side(n, tri[0], p) / den
    if not (0 <= t <= 1):
        return None
    hit = add(p, scale(d, t))
    return hit if point_in_triangle(hit, tri) else None


def dominant_axis(n):
    return max(range(3), key=lambda i: abs(n[i]))


def project(p, drop): return tuple(p[i] for i in range(3) if i != drop)
def orient2(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def on_segment2(a, b, p):
    return orient2(a, b, p) == 0 and min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) \
        and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])


def proper_cross2(a, b, c, d):
    ab_c, ab_d = orient2(a, b, c), orient2(a, b, d)
    cd_a, cd_b = orient2(c, d, a), orient2(c, d, b)
    return ((ab_c > 0 > ab_d or ab_d > 0 > ab_c) and
            (cd_a > 0 > cd_b or cd_b > 0 > cd_a))


def coplanar_overlap(tri_a, tri_b, allowed_points=()):
    """Return (intersects, proper), where proper excludes endpoint-only contact."""
    drop = dominant_axis(normal(tri_a))
    a, b = [project(p, drop) for p in tri_a], [project(p, drop) for p in tri_b]
    touches = False
    for i in range(3):
        for j in range(3):
            p, q = a[i], a[(i + 1) % 3]
            r, s = b[j], b[(j + 1) % 3]
            if proper_cross2(p, q, r, s):
                return True, True
            if on_segment2(p, q, r) or on_segment2(p, q, s) \
                    or on_segment2(r, s, p) or on_segment2(r, s, q):
                # Endpoint/edge contact is dealt with by the combinatorial check;
                # continue because a contained vertex can make this a proper overlap.
                touches = True
    if any(point_in_triangle(p, tri_a) and p not in allowed_points for p in tri_b) or \
            any(point_in_triangle(p, tri_b) and p not in allowed_points for p in tri_a):
        return True, True
    return touches, False


def triangle_intersects(tri_a, tri_b, allowed_points=(), boxes=None):
    """Return (intersects, proper) using exact rational predicates."""
    if boxes is None:
        boxes = (aabb(tri_a), aabb(tri_b))
    if not aabb_overlap(*boxes):
        return False, False
    na, nb = normal(tri_a), normal(tri_b)
    if zero(cross(na, nb)) and plane_side(na, tri_a[0], tri_b[0]) == 0:
        return coplanar_overlap(tri_a, tri_b, allowed_points)
    hits = [segment_triangle_hit(tri_a[i], tri_a[(i + 1) % 3], tri_b) for i in range(3)]
    hits += [segment_triangle_hit(tri_b[i], tri_b[(i + 1) % 3], tri_a) for i in range(3)]
    hits = [h for h in hits if h is not None]
    return bool(hits), any(h not in allowed_points for h in hits)


def _edge_data(faces):
    edges = defaultdict(list)
    for fi, face in enumerate(faces):
        for i in range(3):
            u, v = face[i], face[(i + 1) % 3]
            key = tuple(sorted((u, v)))
            edges[key].append((fi, 1 if (u, v) == key else -1))
    return edges


def _orientability(faces, edges, require_closed):
    adjacency = defaultdict(list)
    defects = []
    for edge, incidences in edges.items():
        if require_closed and len(incidences) != 2:
            defects.append(("edge_incidence", edge, len(incidences)))
        elif len(incidences) == 2 and incidences[0][0] != incidences[1][0]:
            (f, s), (g, t) = incidences
            adjacency[f].append((g, -s * t))
            adjacency[g].append((f, -s * t))
    signs = {}
    for root in range(len(faces)):
        if root in signs:
            continue
        signs[root] = 1
        queue = deque([root])
        while queue:
            f = queue.popleft()
            for g, required in adjacency[f]:
                expected = signs[f] * required
                if g in signs and signs[g] != expected:
                    defects.append(("orientation_cycle", f, g))
                elif g not in signs:
                    signs[g] = expected
                    queue.append(g)
    return not defects, defects


def verify_mesh(vertices, faces, *, require_closed=True):
    """Return exact mesh counts and the first structural/geometric defects."""
    vertices = [qpoint(p) for p in vertices]
    faces = [tuple(face) for face in faces]
    defects = []
    for fi, face in enumerate(faces):
        if len(set(face)) != 3 or any(i < 0 or i >= len(vertices) for i in face):
            defects.append(("invalid_face", fi, face))
        elif zero(normal(tuple(vertices[i] for i in face))):
            defects.append(("degenerate_face", fi, face))
    edges = _edge_data(faces)
    if require_closed:
        for edge, incidence in edges.items():
            if len(incidence) != 2:
                defects.append(("boundary_or_nonmanifold_edge", edge, len(incidence)))
    orientable, orientation_defects = _orientability(faces, edges, require_closed)
    defects.extend(orientation_defects)
    triangles = [tuple(vertices[i] for i in face) for face in faces]
    boxes = [aabb(triangle) for triangle in triangles]
    for i in range(len(triangles)):
        for j in range(i + 1, len(triangles)):
            common = set(faces[i]) & set(faces[j])
            allowed_points = {vertices[k] for k in common}
            hit, proper = triangle_intersects(
                triangles[i], triangles[j], allowed_points, (boxes[i], boxes[j]))
            if not hit:
                continue
            allowed = len(common) in (1, 2)
            if not allowed or proper:
                defects.append(("triangle_intersection", i, j, tuple(sorted(common))))
    return {
        "V": len(vertices), "E": len(edges), "F": len(faces),
        "chi": len(vertices) - len(edges) + len(faces),
        "closed": all(len(v) == 2 for v in edges.values()),
        "orientable": orientable, "embedded": not any(d[0] in ("triangle_intersection", "degenerate_face", "invalid_face") for d in defects),
        "defects": defects,
    }


if __name__ == "__main__":
    # Tetrahedron: a legitimate closed orientable embedded mesh.
    tetra_v = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]
    tetra_f = [(0, 2, 1), (0, 1, 3), (0, 3, 2), (1, 2, 3)]
    assert verify_mesh(tetra_v, tetra_f)["embedded"]
    assert verify_mesh(tetra_v, tetra_f)["orientable"]
    # A pair crossing in their interiors is rejected.
    assert not verify_mesh([(0, 0, 0), (2, 0, 0), (0, 2, 0),
                            (1, -1, -1), (1, 1, 1), (1, 2, -1)],
                           [(0, 1, 2), (3, 4, 5)], require_closed=False)["embedded"]
    # Coplanar overlap is rejected; shared edge and shared vertex are allowed.
    assert not verify_mesh([(0, 0, 0), (2, 0, 0), (0, 2, 0), (1, 0, 0), (1, 1, 0)],
                           [(0, 1, 2), (0, 3, 4)], require_closed=False)["embedded"]
    # A planar square triangulated along its diagonal is a valid shared-edge mesh.
    assert verify_mesh([(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0)],
                       [(0, 1, 2), (0, 2, 3)], require_closed=False)["embedded"]
    # Sharing one vertex without any further contact is also valid.
    assert verify_mesh([(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0)],
                       [(0, 1, 2), (0, 3, 4)], require_closed=False)["embedded"]
    assert verify_mesh([(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)],
                       [(0, 1, 2), (0, 1, 3)], require_closed=False)["embedded"]
    print(verify_mesh(tetra_v, tetra_f))
