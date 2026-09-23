#!/usr/bin/env python3
"""A rational, certificate-carrying two-zero navigation control.

The source is a declared product of quadratic holomorphic generators. Every
boundary segment carries an exact chord-homotopy exclusion certificate; the
signed-ray crossing count therefore equals the analytic boundary winding.
No binary floating-point operations or sampled sign guesses are used.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path


Z = tuple[Q, Q]


def z(x: Q | int, y: Q | int) -> Z:
    return (Q(x), Q(y))


def add(a: Z, b: Z) -> Z:
    return (a[0] + b[0], a[1] + b[1])


def sub(a: Z, b: Z) -> Z:
    return (a[0] - b[0], a[1] - b[1])


def mul(a: Z, b: Z) -> Z:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def dot(a: Z, b: Z) -> Q:
    return a[0] * b[0] + a[1] * b[1]


CENTERS: tuple[Z, Z] = (z(Q(1, 10), Q(1, 16)), z(Q(1, 10), Q(3, 16)))
RADICANDS: tuple[Q, Q] = (Q(1, 2), Q(1, 3))


def generator(point: Z, center: Z, radicand: Q) -> Z:
    delta = sub(point, center)
    return sub(mul(delta, delta), z(radicand, 0))


def source(point: Z) -> Z:
    return mul(
        generator(point, CENTERS[0], RADICANDS[0]),
        generator(point, CENTERS[1], RADICANDS[1]),
    )


def mul_polynomials(a: list[Z], b: list[Z]) -> list[Z]:
    out = [z(0, 0) for _ in range(len(a) + len(b) - 1)]
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = add(out[i + j], mul(ai, bj))
    return out


def segment_error_bound(a: Z, b: Z) -> Q:
    """An exact upper bound on the quartic source's chord error."""
    delta = sub(b, a)
    factors = []
    for center, radicand in zip(CENTERS, RADICANDS):
        base = sub(a, center)
        factors.append(
            [
                sub(mul(base, base), z(radicand, 0)),
                mul(z(2, 0), mul(base, delta)),
                mul(delta, delta),
            ]
        )
    coefficients = mul_polynomials(*factors)
    # |(f(a+t delta))''| <= sum k(k-1)(|Re p_k|+|Im p_k|)
    second_bound = sum(
        k * (k - 1) * (abs(p[0]) + abs(p[1]))
        for k, p in enumerate(coefficients)
        if k >= 2
    )
    # Linear interpolation error is at most sup |P''| / 8 on [0,1].
    return second_bound / 8


def factor_count(low: Q, high: Q) -> int:
    # For each generator, c_x^2 < d < (1-c_x)^2 implies one algebraic
    # root c_x+sqrt(d) in (0,1), and the other c_x-sqrt(d) left of 0.
    for center, radicand in zip(CENTERS, RADICANDS):
        assert 0 < center[0] < 1
        assert center[0] ** 2 < radicand < (1 - center[0]) ** 2
    return sum(low < center[1] < high for center in CENTERS)


def qstr(value: Q) -> str:
    return str(value)


def zjson(point: Z) -> list[str]:
    return [qstr(point[0]), qstr(point[1])]


def chord_distance_sq(a: Z, b: Z) -> Q:
    d = sub(b, a)
    norm = dot(d, d)
    if norm == 0:
        return dot(a, a)
    t = min(Q(1), max(Q(0), -dot(a, d) / norm))
    near = add(a, (t * d[0], t * d[1]))
    return dot(near, near)


@dataclass
class Region:
    low: Q
    high: Q
    # Counterclockwise bottom, right, top, left; every path has its endpoints.
    edges: tuple[list[Z], list[Z], list[Z], list[Z]]


class SourceReceiver:
    def __init__(self) -> None:
        self.values: dict[Z, Z] = {}
        self.attempts = 0
        self.accepted = 0
        self.refused = 0
        self.max_word_bits = 0
        self.witnesses: dict[tuple[Z, Z], tuple[Q, Q]] = {}

    def record_word(self, value: Q) -> None:
        self.max_word_bits = max(
            self.max_word_bits,
            abs(value.numerator).bit_length(),
            value.denominator.bit_length(),
        )

    def value(self, point: Z) -> Z:
        if point not in self.values:
            self.values[point] = source(point)
            for part in (*point, *self.values[point]):
                self.record_word(part)
        return self.values[point]

    def segment(self, a: Z, b: Z) -> list[Z]:
        assert a != b and (a[0] == b[0] or a[1] == b[1])
        self.attempts += 1
        pa, pb = self.value(a), self.value(b)
        min_sq = chord_distance_sq(pa, pb)
        error_sq = segment_error_bound(a, b) ** 2
        self.record_word(min_sq)
        self.record_word(error_sq)
        if min_sq > error_sq:
            self.accepted += 1
            self.witnesses[(a, b)] = (min_sq, error_sq)
            return [a, b]
        self.refused += 1
        middle = z((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
        left = self.segment(a, middle)
        right = self.segment(middle, b)
        return left[:-1] + right

    def initial_region(self) -> Region:
        corners = (z(0, 0), z(1, 0), z(1, 1), z(0, 1))
        paths = tuple(
            self.segment(corners[i], corners[(i + 1) % 4]) for i in range(4)
        )
        return Region(Q(0), Q(1), paths)  # type: ignore[arg-type]

    def part_at(self, path: list[Z], cut: Q) -> tuple[list[Z], list[Z]]:
        for i, point in enumerate(path):
            if point[1] == cut:
                return path[: i + 1], path[i:]
            if i + 1 == len(path):
                break
            following = path[i + 1]
            if (point[1] - cut) * (following[1] - cut) < 0:
                split_point = z(point[0], cut)
                first = self.segment(point, split_point)
                second = self.segment(split_point, following)
                return path[:i] + first, second + path[i + 2 :]
        raise ValueError("cut does not cross side")

    def split(self, region: Region, cut: Q) -> tuple[Region, Region]:
        assert region.low < cut < region.high
        bottom, right, top, left = region.edges
        right_low, right_high = self.part_at(right, cut)
        left_high, left_low = self.part_at(left, cut)
        # This new port is certified once; the upper child takes its reversal.
        shared = self.segment(z(1, cut), z(0, cut))
        lower = Region(region.low, cut, (bottom, right_low, shared, left_low))
        upper = Region(cut, region.high, (list(reversed(shared)), right_high, top, left_high))
        return lower, upper

    def winding(self, region: Region) -> int:
        points: list[Z] = []
        for path in region.edges:
            points += path[:-1]
        assert points and region.edges[0][0] == region.edges[-1][-1]
        values = [self.value(point) for point in points]
        # Pick an exact rational ray avoiding every vertex image.
        direction = next(
            n for n in range(2, 10000) if all(n * v[1] - v[0] != 0 for v in values)
        )
        # Multiplication by (n-i) sends the ray of slope 1/n to the real axis.
        turned = [mul(v, z(direction, -1)) for v in values]
        winding = 0
        for a, b in zip(turned, turned[1:] + turned[:1]):
            if a[1] * b[1] >= 0:
                continue
            x_at_crossing = (a[0] * b[1] - b[0] * a[1]) / (b[1] - a[1])
            self.record_word(x_at_crossing)
            if x_at_crossing > 0:
                winding += 1 if a[1] < 0 else -1
        return winding

    def check_region(self, region: Region) -> int:
        for i in range(4):
            assert region.edges[i][-1] == region.edges[(i + 1) % 4][0]
            for a, b in zip(region.edges[i], region.edges[i][1:]):
                # The segment was certified in either traversal direction.
                assert (a, b) in self.witnesses or (b, a) in self.witnesses
        winding = self.winding(region)
        counted = factor_count(region.low, region.high)
        assert winding == counted, (region.low, region.high, winding, counted)
        return winding

    def receipt_region(self, region: Region, winding: int) -> dict:
        return {
            "y_interval": [qstr(region.low), qstr(region.high)],
            "winding": winding,
            "boundary": [[zjson(point) for point in path] for path in region.edges],
        }

    def receipt_witnesses(self) -> list[dict]:
        return [
            {
                "segment": [zjson(a), zjson(b)],
                "chord_distance_squared": qstr(pair[0]),
                "curve_chord_error_squared_upper": qstr(pair[1]),
            }
            for (a, b), pair in self.witnesses.items()
        ]


def run_policy(name: str) -> dict:
    receiver = SourceReceiver()
    root = receiver.initial_region()
    root_count = receiver.check_region(root)
    assert root_count == 2
    pending = [root]
    cuts: list[dict] = []
    finished: list[Region] = []
    while pending:
        region = pending.pop(0)
        count = receiver.check_region(region)
        if count < 2:
            finished.append(region)
            continue
        if name == "generator_height":
            # The two factor generators are supplied. Their exact receiving
            # heights give a separating port without knowing a numerical zero.
            cut = (CENTERS[0][1] + CENTERS[1][1]) / 2
        elif name == "fixed_midpoint":
            cut = (region.low + region.high) / 2
        else:
            raise ValueError(name)
        lower, upper = receiver.split(region, cut)
        left_count, right_count = receiver.check_region(lower), receiver.check_region(upper)
        assert count == left_count + right_count
        cuts.append(
            {
                "parent": receiver.receipt_region(region, count),
                "cut": qstr(cut),
                "children": [
                    receiver.receipt_region(lower, left_count),
                    receiver.receipt_region(upper, right_count),
                ],
                "port_pair_cancels": lower.edges[2] == list(reversed(upper.edges[0])),
            }
        )
        pending.extend((lower, upper))
    assert sum(receiver.check_region(r) for r in finished) == root_count
    assert sorted(receiver.check_region(r) for r in finished) == [0] * (
        len(finished) - 2
    ) + [1, 1]
    return {
        "policy": name,
        "source_receiving_question": "separate both zero fibres in [0,1] x [0,1]",
        "root": receiver.receipt_region(root, root_count),
        "cuts": cuts,
        "terminal_regions": [
            receiver.receipt_region(r, receiver.check_region(r)) for r in finished
        ],
        "cost": {
            "cuts": len(cuts),
            "new_shared_ports": len(cuts),
            "unique_source_evaluations": len(receiver.values),
            "segment_certification_attempts": receiver.attempts,
            "accepted_segment_certificates": receiver.accepted,
            "refused_segment_attempts": receiver.refused,
            "largest_recorded_rational_word_bits": receiver.max_word_bits,
        },
        "segment_certificates": receiver.receipt_witnesses(),
    }


def main() -> None:
    data = {
        "schema": "holonics.exact-zero-navigation-policy.v1",
        "arithmetic": "Python Fraction; exact rational only",
        "source": "f(z)=((z-(1/10+i/16))^2-1/2)((z-(1/10+3i/16))^2-1/3)",
        "source_kind": "declared product of two quadratic holomorphic generators, each with one irrational-real-coordinate zero in the receiver",
        "receiver": "closed square [0,1] x [0,1], with no boundary roots",
        "segment_law": "min_{t in [0,1]} |(1-t)f(a)+t f(b)|^2 > (sum_{k>=2} k(k-1)(|Re p_k|+|Im p_k|)/8)^2 for f(a+t(b-a))=sum p_k t^k",
        "segment_law_reason": "exact polynomial composition and the linear-interpolation remainder bound sup|P''|/8",
        "winding_law": "exact signed crossings of a rational ray after certified chord homotopy",
        "independent_factor_check": "each quadratic factor has c_x^2<d<(1-c_x)^2, so c_x+sqrt(d) lies in (0,1), c_x-sqrt(d) lies left of 0, and the root heights are the supplied center heights",
        "policies": [run_policy("fixed_midpoint"), run_policy("generator_height")],
    }
    output = Path(__file__).with_name("receipt.json")
    output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({p["policy"]: p["cost"] for p in data["policies"]}, indent=2))
    print(output)


if __name__ == "__main__":
    main()
