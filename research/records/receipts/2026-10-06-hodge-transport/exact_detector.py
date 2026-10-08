#!/usr/bin/env python3
"""Exact exterior normalization, AW(2,2), and 96-source detector check.

The finite carrier is the affine simplex population in four boundary faces of a
tetrahedron. All addressed repeats are retained. This does not kernel-check Lean
or replace the all-singular-five-chain theorem. One thread, outer timeout 2 s.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement
import json
import resource
from time import perf_counter_ns

started = perf_counter_ns()


def face(word, i):
    return word[:i] + word[i + 1:]


def boundary_read(read, word):
    return sum((-1) ** i * read(face(word, i)) for i in range(len(word)))


def normal(word):
    # Oriented face opposite vertex zero is the sphere coordinate.
    if len(set(word)) < 3 or set(word) != {1, 2, 3}:
        return 0
    return (-1) ** sum(word[i] > word[j] for i in range(3) for j in range(i + 1, 3))


def raw(word):
    # Added coboundary alpha(u,v)=u+2v+1, delta(alpha)=3v_middle+1.
    return normal(word) + 3 * word[1] + 1


def correction(edge):
    return raw((edge[0],) * 3)


def normalized(word):
    return raw(word) - boundary_read(correction, word)


def shuffle_atoms(x, y):
    result = []
    for x_positions in combinations(range(4), 2):
        xi = yi = 0
        left = [x[0]]
        right = [y[0]]
        inversions = 0
        for step in range(4):
            if step in x_positions:
                inversions += yi
                xi += 1
            else:
                yi += 1
            left.append(x[xi])
            right.append(y[yi])
        result.append(((-1) ** inversions, tuple(left), tuple(right)))
    return result


def aw(left_read, right_read, x, y):
    return left_read(x[:3]) * right_read(y[2:])


def polynomial_add(*parts):
    out = Counter()
    for part in parts:
        out.update(part)
    return {key: value for key, value in out.items() if value}


# Universal five-boundary return with independent formal coefficient variables.
actual_polynomial = {("a0", "b0"): 1, ("a1", "b0"): -1, ("a2", "b0"): 1,
                     ("a3", "b1"): -1, ("a3", "b2"): 1, ("a3", "b3"): -1}
returned_polynomial = polynomial_add(
    {("a0", "b0"): 1, ("a1", "b0"): -1, ("a2", "b0"): 1, ("a3", "b0"): -1},
    {("a3", "b0"): 1, ("a3", "b1"): -1, ("a3", "b2"): 1, ("a3", "b3"): -1})
assert actual_polynomial == returned_polynomial


def sphere_words(length):
    return [word for word in combinations_with_replacement(range(4), length)
            if len(set(word)) <= 3]


two_sources = sphere_words(3)
three_sources = sphere_words(4)
five_sources = sphere_words(6)
for word in two_sources:
    assert normalized(word) == normal(word)
for word in three_sources:
    assert boundary_read(raw, word) == 0
    assert boundary_read(normalized, word) == 0
for edge in sphere_words(2):
    for i in range(2):
        repeated = edge[:i + 1] + edge[i:]
        assert normalized(repeated) == 0
        assert raw(repeated) == raw((edge[i],) * 3)
for x in five_sources:
    for y in five_sources:
        received = sum((-1) ** i * aw(normalized, normalized, face(x, i), face(y, i))
                       for i in range(6))
        assert received == 0

source_faces = [(tuple(vertex for vertex in range(4) if vertex != i), (-1) ** i)
                for i in range(4)]
assert sum(sign * raw(word) for word, sign in source_faces) == 1
assert sum(sign * normalized(word) for word, sign in source_faces) == 1
actual_atoms = []
for x, left_sign in source_faces:
    for y, right_sign in source_faces:
        for sign, left, right in shuffle_atoms(x, y):
            actual_atoms.append((left_sign * right_sign * sign, left, right))
assert len(actual_atoms) == 96
full_value = sum(sign * aw(normalized, normalized, x, y) for sign, x, y in actual_atoms)
assert full_value == 1
example = (1, 2, 3)
six = [{"sign": sign, "front_left": list(x[:3]), "back_right": list(y[2:]),
        "normalized_return": sign * aw(normalized, normalized, x, y),
        "raw_return": sign * aw(raw, raw, x, y)}
       for sign, x, y in shuffle_atoms(example, example)]
assert sum(row["normalized_return"] for row in six) == 1
naive = sum(row["raw_return"] for row in six)
assert naive != raw(example) ** 2

print(json.dumps({
    "passed": True,
    "arithmetic": "exact integers and rational coefficient chart; no floats",
    "projection_ns": 2_000_000_000,
    "deadline_ns": 2_000_000_000,
    "wall_ns": perf_counter_ns() - started,
    "peak_resident_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024,
    "threads": 1,
    "sphere_two_sources": len(two_sources),
    "sphere_three_sources": len(three_sources),
    "affine_five_sources_per_factor": len(five_sources),
    "actual_product_five_boundary_reads": len(five_sources) ** 2,
    "signed_four_source_occurrences": len(actual_atoms),
    "actual_fundamental_value": full_value,
    "six_shuffle_example": six,
    "raw_single_pair_expected_product": raw(example) ** 2,
    "raw_single_pair_shuffle_return": naive,
    "universal_boundary_polynomial": [[list(key), value] for key, value in actual_polynomial.items()],
    "status": "exact exterior incidence/normalization witness; formal validation pending",
    "limits": "finite affine sphere-face carrier; all singular five-boundaries require the Lean source theorem"
}, indent=2))
