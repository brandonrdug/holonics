"""Exact woven-field bridge inside a witnessed four-torus overlap.

This is an exterior receiver construction.  It maps the existing shorts PL mesh into one
actual four-channel torus-kernel overlap, certifies the complete transformed mesh through an
axis-aligned interval box, and records the local two-field intersection plane and phase-sheet
cycles.  It does not claim that the mesh is a material boundary or that the local plane makes a
global Mobius surface.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import importlib.util
import json
import runpy

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent

woven = runpy.run_path(str(HERE / "woven_ecology.py"))
build = runpy.run_path(str(HERE / "build.py"))
R = woven["r"]
RINGS = woven["RINGS"]
poly = woven["poly"]
phase = woven["phase"]
shorts = build["shorts"]


def wire(value):
    if isinstance(value, Q):
        return [str(value.numerator), str(value.denominator)]
    if isinstance(value, dict):
        return {str(k): wire(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [wire(v) for v in value]
    return value


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def interval_mul(a, b):
    values = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(values), max(values)


def interval_square(a):
    if a[0] <= 0 <= a[1]:
        return Q(0), max(a[0] * a[0], a[1] * a[1])
    return min(a[0] * a[0], a[1] * a[1]), max(a[0] * a[0], a[1] * a[1])


def affine_point(center, eps, frame, source):
    return tuple(center[i] + eps * sum(source[k] * frame[k][i] for k in range(3))
                 for i in range(3))


def box_interval(points):
    lo = tuple(min(p[i] for p in points) for i in range(3))
    hi = tuple(max(p[i] for p in points) for i in range(3))
    return tuple((lo[i], hi[i]) for i in range(3))


def torus_poly_upper(ring, box):
    shifted = []
    for axis in range(3):
        shifted.append((box[axis][0] - ring["center"] if axis == ring["axis"] else box[axis][0],
                        box[axis][1] - ring["center"] if axis == ring["axis"] else box[axis][1]))
    squares = [interval_square(v) for v in shifted]
    s = (Q(0), Q(0))
    for value in squares:
        s = interval_add(s, value)
    Rr = Q(ring["radius"])
    minor = Q(MINOR)
    A = interval_add(s, (Rr * Rr - minor * minor, Rr * Rr - minor * minor))
    plane = (Q(0), Q(0))
    for axis, value in enumerate(squares):
        if axis != ring["axis"]:
            plane = interval_add(plane, value)
    Asq = interval_square(A)
    return Asq[1] - 4 * Rr * Rr * plane[0]


def gradient(ring, point):
    shifted = [point[i] - (ring["center"] if i == ring["axis"] else 0) for i in range(3)]
    radius = Q(ring["radius"])
    minor = Q(MINOR)
    s = sum(v * v for v in shifted)
    A = s + radius * radius - minor * minor
    return tuple(4 * A * shifted[i] -
                 (8 * radius * radius * shifted[i] if i != ring["axis"] else 0)
                 for i in range(3))


def gradient_interval(ring, box):
    shifted = []
    for axis in range(3):
        shifted.append((box[axis][0] - (ring["center"] if axis == ring["axis"] else 0),
                        box[axis][1] - (ring["center"] if axis == ring["axis"] else 0)))
    squares = [interval_square(v) for v in shifted]
    s = (Q(0), Q(0))
    for value in squares:
        s = interval_add(s, value)
    radius = Q(ring["radius"])
    minor = Q(MINOR)
    A = interval_add(s, (radius * radius - minor * minor, radius * radius - minor * minor))
    result = []
    for i, value in enumerate(shifted):
        term = interval_mul((4, 4), interval_mul(A, value))
        if i != ring["axis"]:
            term = interval_sub(term, interval_mul((8 * radius * radius, 8 * radius * radius), value))
        result.append(term)
    return tuple(result)


MINOR = Q(woven["MINOR"])


def normalize(v):
    scale = max(abs(x) for x in v)
    assert scale
    return tuple(x / scale for x in v)


def local_plane(ri, rj, site, box):
    gi, gj = gradient(RINGS[ri], site), gradient(RINGS[rj], site)
    ni, nj = normalize(gi), normalize(gj)
    tangent = normalize(R.cross(gi, gj))
    normal = ni
    second = normalize(R.cross(normal, tangent))
    residual = []
    for ring in (RINGS[ri], RINGS[rj]):
        g0 = gradient(ring, site)
        bounds = gradient_interval(ring, box)
        residual.append(tuple(max(abs(bounds[k][0] - g0[k]), abs(bounds[k][1] - g0[k]))
                              for k in range(3)))
    return dict(gradient_i=gi, gradient_j=gj, normal_i=ni, normal_j=nj,
                tangent_basis=tangent, normal=normal, second_tangent_basis=second,
                first_order_gradient_residual=residual,
                first_order_residual_bound=max(max(row) for row in residual))


def choose_site(data):
    """Select the four-channel site by the weakest normalized kernel support."""
    grid = data[0]
    candidates = []
    for point in grid:
        positive = [i for i, ring in enumerate(RINGS) if poly(ring, point) < 0]
        if len(positive) < 4:
            continue
        for quartet in combinations(positive, 4):
            strengths = [(-poly(RINGS[i], point)) /
                         (4 * RINGS[i]["radius"] ** 2 * int(MINOR) ** 2)
                         for i in quartet]
            candidates.append((min(strengths), point, quartet, positive))
    assert candidates
    _, site, quartet, positive = max(
        candidates, key=lambda row: (row[0], tuple(-x for x in row[1]), row[2]))
    return site, quartet


def source_ports(vertices):
    """The four shared disk/ribbon endpoint ports in build.shorts('shorts')."""
    ports = {}
    for band, offset in (("a", 0), ("b", 72)):
        ports[f"{band}_start"] = tuple(9 * (2 + j) + (0 if band == "a" else 2 + j)
                                        for j in range(5)) if band == "a" else tuple(2 + j for j in range(5))
        ports[f"{band}_end"] = tuple(9 * (6 - j) + 8 for j in range(5)) if band == "a" else tuple(72 + 2 + j for j in range(5))
    for key, ids in ports.items():
        assert all(0 <= i < len(vertices) for i in ids), (key, ids)
    return ports


def directed_phase(i, j, site):
    left, right = phase(RINGS[i], site), phase(RINGS[j], site)
    # The directed edge carries phase(source) * conjugate(phase(target)); retaining
    # the actual common site makes the cycle telescope before the declared sheet sign.
    return R.cm(left, (right[0], -right[1]))


def cycle_product(cycle, site, sheet_sign):
    value = (Q(1), Q(0))
    for i, j in zip(cycle, cycle[1:] + cycle[:1]):
        value = R.cm(value, directed_phase(i, j, site))
    return R.cm(value, (Q(sheet_sign), Q(0)))


def main():
    grid, _, _, _ = woven["scene_lattice"]()
    site, quartet = choose_site((grid,))
    positive = [i for i, ring in enumerate(RINGS) if poly(ring, site) < 0]
    normalized_support = min(
        (-poly(RINGS[i], site)) /
        (4 * RINGS[i]["radius"] ** 2 * int(MINOR) ** 2) for i in quartet)
    vertices, faces = shorts("shorts")
    orient_path = ROOT / "research/papers/source/papers/hnn-information-chemistry/orientation-example.py"
    spec = importlib.util.spec_from_file_location("orientation_witness", orient_path)
    orientation = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(orientation)
    source_orientation, _ = orientation.inspect(faces)
    pair = None
    for candidate in combinations(quartet, 2):
        cross = R.cross(gradient(RINGS[candidate[0]], site),
                        gradient(RINGS[candidate[1]], site))
        if R.dot(cross, cross) != 0:
            pair = candidate
            break
    assert pair is not None
    gi, gj = gradient(RINGS[pair[0]], site), gradient(RINGS[pair[1]], site)
    normal = normalize(gi)
    tangent = normalize(R.cross(gi, gj))
    second = normalize(R.cross(normal, tangent))
    frame = (tangent, second, normal)
    determinant = R.dot(frame[0], R.cross(frame[1], frame[2]))
    assert determinant > 0
    eps = MINOR / 4
    while True:
        mapped = [affine_point(site, eps, frame, vertex) for vertex in vertices]
        box = box_interval(mapped)
        uppers = [torus_poly_upper(RINGS[i], box) for i in quartet]
        if all(upper < 0 for upper in uppers):
            break
        eps /= 2
        assert eps > 0
    # Degenerate boxes must reproduce the source polynomial exactly; this catches any
    # discrepancy between the interval enclosure and the defining torus polynomial.
    for point in (site, tuple(site[i] + eps * vertices[0][i] for i in range(3)),
                  tuple(site[i] + eps * vertices[-1][i] for i in range(3))):
        point_box = tuple((value, value) for value in point)
        for ring in RINGS[:5] + RINGS[-2:]:
            assert torus_poly_upper(ring, point_box) == poly(ring, point)
    assert all(poly(RINGS[i], p) < 0 for p in mapped for i in quartet)
    # The AABB certificate is stronger than vertex membership: every point of every triangle
    # lies in the box, and each polynomial's interval upper bound is strictly negative there.
    local = local_plane(pair[0], pair[1], site, box)
    max_l1_delta = max(sum(abs(point[k] - site[k]) for k in range(3)) for point in mapped)
    residual_bounds, value_residual_bounds = {}, {}
    for ring in quartet:
        g0 = gradient(RINGS[ring], site)
        gbox = gradient_interval(RINGS[ring], box)
        gradvar = max(max(abs(gbox[k][0] - g0[k]), abs(gbox[k][1] - g0[k]))
                      for k in range(3))
        bound = gradvar * max_l1_delta
        residual_bounds[ring] = gradvar
        value_residual_bounds[ring] = bound
        for point in mapped:
            delta = tuple(point[k] - site[k] for k in range(3))
            actual = abs(poly(RINGS[ring], point) - poly(RINGS[ring], site) - R.dot(g0, delta))
            assert actual <= bound
    labels = dict(zip(quartet, "abcd"))
    abc = (quartet[0], quartet[1], quartet[2])
    abd = (quartet[0], quartet[1], quartet[3])
    products = dict(abc=cycle_product(abc, site, -1), abd=cycle_product(abd, site, 1))
    assert products["abc"] == (Q(-1), Q(0))
    assert products["abd"] == (Q(1), Q(0))
    result = dict(
        schema="woven-four-torus-overlap.v1",
        scope="exact finite field passage inside a witnessed overlap; not a material-boundary or global nonorientability claim",
        source_geometry={"kind": "build.shorts('shorts')", "vertices": len(vertices), "triangles": len(faces),
                         "attachment_ports": source_ports(vertices), "orientation": source_orientation},
        scene={"site": site, "positive_channels_at_site": positive, "selected_quartet": quartet,
               "selection": "maximized minimum normalized kernel support over four-channel quartets",
               "selected_min_normalized_support": normalized_support},
        support={"scale": eps, "aabb": box, "polynomial_upper_bounds": dict(zip(quartet, uppers)),
                 "physical_scale": eps / woven["SCALE"],
                 "all_transformed_vertices_inside": True, "all_mesh_triangles_inside_by_aabb": True},
        source_geometry_mapped={"vertices": mapped, "source_coordinates": vertices, "faces": faces},
        affine_frame={"columns": frame, "normal": normal, "tangent": tangent,
                      "second_tangent": second, "determinant": determinant},
        local_plane={"pair": pair, **local, "max_l1_delta": max_l1_delta,
                     "gradient_variation_bounds": residual_bounds,
                     "first_order_value_residual_bounds": value_residual_bounds},
        orientation_sheet_cycles={"labels": labels, "abc_minus_edge_ca": True, "abd_all_plus": True,
                                  "products": products, "telescope_at_common_site": True},
    )
    out = HERE / "woven_bridge_receipt.json"
    out.write_text(json.dumps(wire(result), indent=2) + "\n")
    print(json.dumps(wire({"output": str(out), "site": site, "quartet": quartet,
                           "physical_scale": eps / woven["SCALE"], "triangles": len(faces), "products": products}), indent=2))


if __name__ == "__main__":
    main()
