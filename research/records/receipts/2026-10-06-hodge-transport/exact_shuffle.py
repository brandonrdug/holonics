"""Exact addressed shuffle incidence, exterior verification of the proposed source law."""
from collections import Counter
from itertools import combinations
from json import dumps
from time import perf_counter_ns
import resource

def shuffles(p, q):
    for left_steps in combinations(range(p + q), p):
        a = b = inversions = 0
        vertices = [(a, b)]
        for step in range(p + q):
            if step in left_steps:
                inversions += b
                a += 1
            else:
                b += 1
            vertices.append((a, b))
        yield tuple(vertices), (-1) ** inversions

def product_current(left, right):
    result = Counter()
    for lv, lc in left.items():
        for rv, rc in right.items():
            for path, sign in shuffles(len(lv) - 1, len(rv) - 1):
                result[tuple((lv[a], rv[b]) for a, b in path)] += lc * rc * sign
    return result

def boundary(current):
    result = Counter()
    for simplex, coefficient in current.items():
        for face in range(len(simplex)):
            result[simplex[:face] + simplex[face + 1:]] += coefficient * (-1) ** face
    return result

def clean(current):
    return {s: c for s, c in current.items() if c != 0}

start = perf_counter_ns()
triangle = Counter({(0, 1, 2): 1})
lhs = boundary(product_current(triangle, triangle))
rhs = product_current(boundary(triangle), triangle)
rhs.update(product_current(triangle, boundary(triangle)))
assert clean(lhs) == clean(rhs)
fundamental = Counter({tuple(v for v in range(4) if v != face): (-1) ** face
                       for face in range(4)})
assert not clean(boundary(fundamental))
source = product_current(fundamental, fundamental)
source_boundary = boundary(source)
assert len(clean(source)) == 4 * 4 * 6
assert not clean(source_boundary)
print(dumps({
    "scope": "finite exact affine source-map incidence; not a Lean receipt or nonboundary theorem",
    "shuffle_paths": [{"vertices": p, "sign": s} for p, s in shuffles(2, 2)],
    "single_pair_boundary_faces_before_cancellation": 6 * 5,
    "single_pair_boundary_faces_after_cancellation": len(clean(lhs)),
    "product_fundamental_source_occurrences": len(clean(source)),
    "source_boundary_faces_before_cancellation": 4 * 4 * 6 * 5,
    "source_boundary_faces_after_cancellation": len(clean(source_boundary)),
    "zero_test": "every coefficient exactly zero, integer arithmetic",
    "wall_ns": perf_counter_ns() - start,
    "peak_resident_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024,
    "outer_deadline_ns": 2_000_000_000,
    "threads": 1
}, indent=2))
