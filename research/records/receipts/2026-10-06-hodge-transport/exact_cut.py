"""Exterior exact witness of existing finite Hodge receivers; no HNN routine."""
from fractions import Fraction as Q
import json
import resource
import time

started = time.monotonic_ns()


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def sub(x, y):
    return tuple(a - b for a, b in zip(x, y))


def scale(a, x):
    return tuple(a * b for b in x)


def boundary(x, weights=(1, 1, 1, 1)):
    return tuple(weights[(i - 1) % 4] * x[(i - 1) % 4] - weights[i] * x[i]
                 for i in range(4))


def coboundary(p):
    return tuple(p[(i + 1) % 4] - p[i] for i in range(4))


def laplacian(x, weights=(1, 1, 1, 1)):
    return coboundary(boundary(x, weights))


def cut(x):
    return (x[0], x[1], Q(0), Q(0))


def left_energy(x):
    return sum(a * a for a in x[:2])


def heat(a, x):
    return sub(x, scale(a, laplacian(x)))


x = tuple(map(Q, (1, 2, 3, 4)))
h = (Q(5, 2),) * 4
e = sub(x, h)
assert e == coboundary(tuple(map(Q, (0, Q(-3, 2), -2, Q(-3, 2)))))
assert boundary(h) == (0,) * 4
assert sum(a * b for a, b in zip(h, e)) == 0
assert left_energy(x) == 5
assert left_energy(h) == Q(25, 2)
assert left_energy(e) == Q(5, 2)
assert 2 * sum(a * b for a, b in zip(h[:2], e[:2])) == -10
defect = sub(laplacian(cut(h)), cut(laplacian(h)))
assert defect == (Q(5, 2), Q(5, 2), Q(-5, 2), Q(-5, 2))
step = Q(1, 8)
assert sub(cut(heat(step, h)), heat(step, cut(h))) == scale(step, defect)
assert scale(step, defect) == (Q(5, 16), Q(5, 16), Q(-5, 16), Q(-5, 16))

# Two actual receivers/sections on the same current, quadratic receiving face.
pair = (Q(3, 2), Q(7, 2))
resolved = (pair[0], pair[0], pair[1], pair[1])
first_defect = left_energy(x) - left_energy(resolved)
second_defect = left_energy(resolved) - left_energy(h)
assert (first_defect, second_defect) == (Q(1, 2), Q(-8))
lower_remainder = sub(resolved, h)
assert left_energy(lower_remainder) == 2
assert second_defect - left_energy(lower_remainder) == -10
assert left_energy(x) == left_energy(h) + first_defect + second_defect

# Changed metric: same circulation class, different harmonic representative.
w = tuple(map(Q, (1, 2, 3, 4)))
c = sum(x) / sum(1 / wi for wi in w)
hw = tuple(c / wi for wi in w)
assert hw == (Q(24, 5), Q(12, 5), Q(8, 5), Q(6, 5))
assert boundary(hw, w) == (0,) * 4
assert sum(hw) == sum(x) == 10
assert sub(x, hw) == coboundary((Q(0), Q(-19, 5), Q(-21, 5), Q(-14, 5)))
assert sum(wi * hi * hi for wi, hi in zip(w, hw)) == 48
assert sum(wi * xi * xi for wi, xi in zip(w, x)) == 100

# Actual first jet of the normalized harmonic receiver for w_i(t)=1+i*t.
# A=sum_i 1/w_i, c=10/A; at zero A=4 and A'=-6, so c'=15/4.
hdot = tuple(Q(15, 4) - Q(5, 2) * i for i in range(4))
assert hdot == (Q(15, 4), Q(5, 4), Q(-5, 4), Q(-15, 4))
assert sum(hdot) == 0
assert boundary(hdot) != (0,) * 4

def face(v):
    if isinstance(v, (tuple, list)):
        return [face(a) for a in v]
    return str(v)


print(json.dumps({
    "scope": "exterior rational development witness; no Lean acceptance or NS regularity",
    "source": face(x), "harmonic": face(h), "exact": face(e),
    "laplacian_cut_defect": face(defect), "step": face(step),
    "heat_commutation_difference": face(scale(step, defect)),
    "left_energy": "5", "harmonic_left_energy": "25/2",
    "first_recursive_defect": face(first_defect),
    "second_recursive_pivot_defect": face(second_defect),
    "lower_remainder_energy": "2", "missing_mixed_term": "-10",
    "changed_weights": face(w), "changed_harmonic": face(hw),
    "changed_harmonic_energy": "48 = 2^4*3",
    "changed_total_energy": "100 = 2^2*5^2",
    "harmonic_receiver_first_jet_at_unit_weights": face(hdot),
    "threads": 1, "wall_ns": time.monotonic_ns() - started,
    "peak_resident_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024,
    "run_kind": "bounded development measurement", "outer_deadline_ns": 2000000000,
}, indent=2))
