"""Exact cold diagnostic of a saved candidate and its original ball; no native mutation.

Usage: python check_affine_separator.py candidate-N.affine.json source.json
The candidate comes from conversation_coupled inspect. Coordinates are its declared
realification of the original joint anchor, not symbol identities or semantic labels.
"""
import json
import sys
from collections import defaultdict
from fractions import Fraction


def integer(value):
    sign, limbs = value
    return sign * sum(limb << (32 * i) for i, limb in enumerate(limbs))


def rational(value):
    return Fraction(integer(value[0]), integer(value[1]))


def separator(candidate, source):
    affine = candidate["predecessor_reading"]["Plural"]
    particular = list(map(rational, affine["particular"]))
    directions = [list(map(rational, row)) for row in affine["directions"]]
    ball = source["anchor"]
    center = [rational(v[k]) for v in ball["center"] for k in ("real", "imaginary")]
    radius = rational(ball["radius"])
    assert len(particular) == 2 + 2 * len(center)
    assert all(len(row) == len(particular) for row in directions)
    classes = defaultdict(list)
    for i in range(len(center)):
        classes[(particular[2 + i], tuple(v[2 + i] for v in directions))].append(i)
    witnesses = []
    for indices in classes.values():
        if len(indices) < 2:
            continue
        minus = min(indices, key=lambda i: center[i])
        plus = max(indices, key=lambda i: center[i])
        gap = center[plus] - center[minus]
        # The normal e_plus-e_minus has squared Euclidean norm two.
        if gap * gap > 2 * radius * radius:
            witnesses.append((gap * gap / 2, plus, minus, gap))
    if not witnesses:
        return {"separator_found": False, "scope": "This search is incomplete; no support claim."}
    bound, plus, minus, gap = max(witnesses)
    return {
        "separator_found": True,
        "plus_coordinate": plus,
        "minus_coordinate": minus,
        "affine_directions": len(directions),
        "particular_annihilated": particular[2 + plus] == particular[2 + minus],
        "every_direction_annihilated": all(v[2 + plus] == v[2 + minus] for v in directions),
        "source_gap": str(gap),
        "distance_squared_lower_bound": str(bound),
        "anchor_radius_squared": str(radius * radius),
        "strictly_separates": bound > radius * radius,
        "scope": "Exact cold separating-plane witness; not a native support receiver or publication.",
    }


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        candidate = json.load(f)
    with open(sys.argv[2]) as f:
        source = json.load(f)
    print(json.dumps(separator(candidate, source), indent=2))
