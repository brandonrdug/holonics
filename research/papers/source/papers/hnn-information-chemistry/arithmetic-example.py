"""Exact exterior chart for the string/tetrahedron/reflection plates.

The grammar is an explicitly declared arithmetic codec, not a native HNN parser
or evidence of learned arithmetic. Rendering consumes these rational coordinates.
Run from this directory, or anywhere: python3 path/to/arithmetic-example.py.
"""
from fractions import Fraction as Q
from functools import reduce
from math import lcm
from pathlib import Path
import json
import re

VERTICES = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
PATTERN = re.compile(r"(0|[1-9][0-9]*)\+(0|[1-9][0-9]*)=(0|[1-9][0-9]*)")


def dot(a, b):
    return sum(x*y for x, y in zip(a, b, strict=True))


def encode(values):
    a, b, c = map(Q, values)
    mass = a+b+c+1
    assert mass > 0
    weights = (a/mass, b/mass, c/mass, 1/mass)
    point = tuple(sum(weights[k]*VERTICES[k][j] for k in range(4)) for j in range(3))
    return point, mass, weights


def decode(point):
    weights = tuple((1+dot(v, point))/4 for v in VERTICES)
    assert weights[3] > 0
    return tuple(w/weights[3] for w in weights[:3])


def residual(values):
    a, b, c = values
    return a+b-c


def geometric_residual(p):
    x, y, z = p
    return (1+3*x-y+z)/(1-x-y+z)


def reflect(values):
    a, b, c = values
    return a, b, 2*(a+b)-c


def midpoint(a, b):
    return tuple((x+y)/2 for x, y in zip(a, b, strict=True))


def vector_wire(v):
    den = reduce(lcm, (x.denominator for x in v), 1)
    return {"num": [int(x*den) for x in v], "den": den}


# Exact regularity: squared edge length 8, norm squared 3, pairwise inner product -1.
for i, v in enumerate(VERTICES):
    assert dot(v, v) == 3
    for j, w in enumerate(VERTICES):
        if i != j:
            assert dot(v, w) == -1
            assert sum((x-y)**2 for x, y in zip(v, w)) == 8

rows = []
for label, source in zip("ABC", ("1+2=3", "2+1=3", "1+2=4"), strict=True):
    match = PATTERN.fullmatch(source)
    assert match is not None
    values = tuple(map(Q, match.groups()))
    point, mass, weights = encode(values)
    assert decode(point) == values
    assert geometric_residual(point) == residual(values)
    rows.append({"label": label, "source": source, "values": [int(x) for x in values],
                 "mass": int(mass), "point": vector_wire(point),
                 "barycentric": vector_wire(weights), "residual": int(residual(values))})

x = tuple(map(Q, (1, 2, 4)))
reflected = reflect(x)
closed = midpoint(x, reflected)
p, m, _ = encode(x)
pr, mr, _ = encode(reflected)
pc, mc, _ = encode(closed)
assert reflect(reflected) == x
assert reflected == (1, 2, 2) and closed == (1, 2, 3)
assert residual(reflected) == -residual(x)
assert residual(closed) == 0
transported = tuple((m*u+mr*v)/(m+mr) for u, v in zip(p, pr, strict=True))
assert transported == pc
naive = midpoint(p, pr)
assert decode(naive) == (Q(1), Q(2), Q(20, 7))
assert geometric_residual(naive) == Q(1, 7)
assert rows[0]["point"] != rows[1]["point"]

_, _, l_source = encode(x)
_, _, l_reflected = encode(reflected)
_, _, l_closed = encode(closed)
_, _, l_naive = encode(decode(naive))
l_difference = tuple(a-b for a, b in zip(l_naive, l_closed, strict=True))
assert sum(abs(x) for x in l_difference) == Q(1, 42)
assert tuple((m*a+mr*b)/(m+mr) for a,b in zip(l_source,l_reflected,strict=True)) == l_closed

# The input-port swap is realized by coordinate transpose for this modal binding.
new_modes = ((2,1),(1,2),(1,1),(2,2))
port_swap = (1,0,2,3)
assert tuple((n,m) for m,n in new_modes) == tuple(new_modes[k] for k in port_swap)
N = 2**4
neighbors = lambda i,j: {(x,y) for x,y in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)) if 1<=x<=N and 1<=y<=N}
for i in range(1,N+1):
    for j in range(1,N+1):
        assert {(y,x) for x,y in neighbors(i,j)} == neighbors(j,i)

# The native primary doctrine's algebra, at an explicit exterior complex receiver.
def primary(x,y):
    p=(x*x,y*y,(x+y)*(x+y))
    total=sum(p)
    return tuple(z/(1+total) for z in p), total/(1+total), 1/(1+total)
color_controls=[]
for gx,gy in ((Q(1),Q(0)),(Q(0),Q(1)),(Q(1),Q(-1)),(Q(1),Q(1)),(Q(2,3),Q(-1,5))):
    rgb,alpha,transmittance=primary(gx,gy)
    assert sum(rgb)==alpha and alpha+transmittance==1
    swapped=primary(gy,gx)[0]
    assert swapped==(rgb[1],rgb[0],rgb[2])
    assert primary(-gx,-gy)==primary(gx,gy)
    color_controls.append({"gradient": vector_wire((gx,gy)), "primaries": vector_wire(rgb),
                           "alpha": [alpha.numerator,alpha.denominator]})

# Boundary of every oriented triangle cancels; a scalar gradient has zero circulation.
for tri in (((0,0),(1,0),(1,1)),((0,0),(1,1),(0,1))):
    f=lambda p: Q(p[0]*p[0]+2*p[1]+p[0]*p[1])
    assert sum(f(tri[(k+1)%3])-f(tri[k]) for k in range(3))==0

result = {
    "scope": "exact rational exterior arithmetic chart; no learned HNN arithmetic claim",
    "vertices": VERTICES,
    "field": {
        "lattice_bits": 4,
        "basis_modes": [[2,1],[1,2],[1,1],[2,2]],
        "historical_basis_modes": [[1,1],[2,1],[1,2],[2,2]],
        "reflection_cases": [vector_wire(w) for w in (l_source,l_reflected,l_closed,l_naive)],
        "difference_weights": vector_wire(l_difference),
        "current_difference_bound": [1,42],
        "intensity_difference_bound": [1,21],
        "current_difference_display_gain": 42,
        "intensity_display": "I_N with fixed reference 1, independent of the source population",
        "intensity_difference_display": "difference / its infinity norm at N steps",
    },
    "rows": rows,
    "receiver_controls": {
        "port_swap": port_swap, "transpose_commutes_with_all_grid_rows": True,
        "primary_response": color_controls,
        "scalar_gradient_triangle_circulation": 0,
        "opaque_display": "quadratic primaries divided by their largest channel; zero is neutral",
        "surface": "piecewise affine graph z=u over two triangles per grid square",
    },
    "reflection": {
        "source": list(map(int, x)), "reflected": list(map(int, reflected)),
        "closed": list(map(int, closed)), "mass_source": int(m), "mass_reflected": int(mr),
        "source_point": vector_wire(p), "reflected_point": vector_wire(pr),
        "closed_point": vector_wire(pc), "naive_point": vector_wire(naive),
        "naive_decoded": vector_wire(decode(naive)),
        "naive_residual": [1, 7], "commuting_difference": [0, 0, 0],
    },
}
Path(__file__).with_name("arithmetic-example.json").write_text(json.dumps(result, indent=2)+"\n")
print("Returned: regular tetrahedron; three source round trips; exact face map; reflection closure; transported update commutes; naive midpoint defect = 1/7; field bounds = 1/42, 1/21; modal/transport transpose; primary-response covariance; scalar-gradient circulation = 0.")
