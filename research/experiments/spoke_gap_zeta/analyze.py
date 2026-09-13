#!/usr/bin/env python3
"""Measure fixed-ray layer gaps in the current polygon-pursuit candidate.

The construction is an exterior geometric reference.  It uses high-precision
mpmath arithmetic for a stable numerical receipt, not an outward-rounded
interval proof.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80

ROOT = Path(__file__).resolve().parent
UPDATES = 100
T = mp.mpf(15) / 100
RAY_COUNT = 8
RAY_ANGLES = [-mp.pi / 2 + 2 * mp.pi * index / RAY_COUNT for index in range(RAY_COUNT)]


def point(x: mp.mpf, y: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    return x, y


def add(a: tuple[mp.mpf, mp.mpf], b: tuple[mp.mpf, mp.mpf]) -> tuple[mp.mpf, mp.mpf]:
    return a[0] + b[0], a[1] + b[1]


def scale(c: mp.mpf, a: tuple[mp.mpf, mp.mpf]) -> tuple[mp.mpf, mp.mpf]:
    return c * a[0], c * a[1]


def sub(a: tuple[mp.mpf, mp.mpf], b: tuple[mp.mpf, mp.mpf]) -> tuple[mp.mpf, mp.mpf]:
    return a[0] - b[0], a[1] - b[1]


def cross(a: tuple[mp.mpf, mp.mpf], b: tuple[mp.mpf, mp.mpf]) -> mp.mpf:
    return a[0] * b[1] - a[1] * b[0]


def fmt(value: mp.mpf) -> str:
    return mp.nstr(value, 50)


def regular_polygon(n: int) -> list[tuple[mp.mpf, mp.mpf]]:
    return [
        point(mp.cos(-mp.pi / 2 + 2 * mp.pi * index / n), mp.sin(-mp.pi / 2 + 2 * mp.pi * index / n))
        for index in range(n)
    ]


def pursuit_layers(n: int) -> list[list[tuple[mp.mpf, mp.mpf]]]:
    layers = [regular_polygon(n)]
    current = layers[0]
    for _ in range(UPDATES):
        current = [
            add(scale(1 - T, current[index]), scale(T, current[(index + 1) % n]))
            for index in range(n)
        ]
        layers.append(current)
    return layers


def ray_polygon_intersections(
    direction: tuple[mp.mpf, mp.mpf], polygon: list[tuple[mp.mpf, mp.mpf]]
) -> list[mp.mpf]:
    """Return deduplicated nonnegative ray/segment distances from the origin."""
    distances: list[mp.mpf] = []
    for index, a in enumerate(polygon):
        b = polygon[(index + 1) % len(polygon)]
        edge = sub(b, a)
        denominator = cross(direction, edge)
        if abs(denominator) < mp.mpf("1e-70"):
            continue
        distance = cross(a, edge) / denominator
        along_edge = cross(a, direction) / denominator
        if distance >= -mp.mpf("1e-60") and -mp.mpf("1e-60") <= along_edge <= 1 + mp.mpf("1e-60"):
            distances.append(max(mp.mpf(0), distance))
    distances.sort()
    unique: list[mp.mpf] = []
    for distance in distances:
        if not unique or distance - unique[-1] > mp.mpf("1e-60"):
            unique.append(distance)
    return unique


def ray_polygon_radius(direction: tuple[mp.mpf, mp.mpf], polygon: list[tuple[mp.mpf, mp.mpf]]) -> mp.mpf:
    intersections = ray_polygon_intersections(direction, polygon)
    if not intersections:
        raise ValueError("ray missed polygon")
    positive = [distance for distance in intersections if distance > mp.mpf("1e-60")]
    return positive[0] if positive else intersections[0]


def mean(values: list[mp.mpf]) -> mp.mpf:
    return sum(values, mp.mpf(0)) / len(values)


def standard_deviation(values: list[mp.mpf]) -> mp.mpf:
    centre = mean(values)
    return mp.sqrt(mean([(value - centre) ** 2 for value in values]))


def lag1(values: list[mp.mpf]) -> mp.mpf | None:
    if len(values) < 3:
        return None
    left, right = values[:-1], values[1:]
    left_mean, right_mean = mean(left), mean(right)
    numerator = sum((a - left_mean) * (b - right_mean) for a, b in zip(left, right))
    denominator = mp.sqrt(
        sum((a - left_mean) ** 2 for a in left) * sum((b - right_mean) ** 2 for b in right)
    )
    return None if denominator == 0 else numerator / denominator


def lag1_within_series(series: list[list[mp.mpf]]) -> tuple[mp.mpf | None, int, mp.mpf | None, mp.mpf | None]:
    """Correlate only adjacent pairs within each spoke, never across spoke joins."""
    left = [value for values in series for value in values[:-1]]
    right = [value for values in series for value in values[1:]]
    if len(left) < 3:
        return None, len(left), None, None
    left_mean, right_mean = mean(left), mean(right)
    numerator = sum((a - left_mean) * (b - right_mean) for a, b in zip(left, right))
    denominator = mp.sqrt(
        sum((a - left_mean) ** 2 for a in left) * sum((b - right_mean) ** 2 for b in right)
    )
    return None if denominator == 0 else numerator / denominator, len(left), left_mean, right_mean


def summary(values: list[mp.mpf], lag_series: list[list[mp.mpf]] | None = None) -> dict[str, str | int | None]:
    centre = mean(values)
    deviation = standard_deviation(values)
    if lag_series is None:
        correlation = lag1(values)
        lag_pair_count, lag_left_mean, lag_right_mean = None, None, None
    else:
        correlation, lag_pair_count, lag_left_mean, lag_right_mean = lag1_within_series(lag_series)
    return {
        "count": len(values),
        "min": fmt(min(values)),
        "mean": fmt(centre),
        "max": fmt(max(values)),
        "std": fmt(deviation),
        "cv": fmt(deviation / abs(centre)) if centre else None,
        "lag1": fmt(correlation) if correlation is not None else None,
        "lag1_pair_count": lag_pair_count,
        "lag1_left_mean": fmt(lag_left_mean) if lag_left_mean is not None else None,
        "lag1_right_mean": fmt(lag_right_mean) if lag_right_mean is not None else None,
    }


def zeta_comparison(gaps: list[mp.mpf], q: mp.mpf) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for exponent in (1, 2):
        power_sum = sum((gap ** exponent for gap in gaps), mp.mpf(0))
        g0_power = gaps[0] ** exponent
        ideal_finite = sum((g0_power * q ** (exponent * index) for index in range(UPDATES)), mp.mpf(0))
        ideal_infinite = g0_power / (1 - q**exponent)
        tail = g0_power * q ** (exponent * UPDATES) / (1 - q**exponent)
        result[str(exponent)] = {
            "measured_finite_sum": fmt(power_sum),
            "ideal_logspiral_finite_sum": fmt(ideal_finite),
            "ideal_gap_zeta_infinite_sum": fmt(ideal_infinite),
            "ideal_tail_after_100": fmt(tail),
        }
    return result


def analyze_case(n: int) -> dict[str, object]:
    layers = pursuit_layers(n)
    directions = [(mp.cos(angle), mp.sin(angle)) for angle in RAY_ANGLES]
    radii = [[ray_polygon_radius(direction, layer) for direction in directions] for layer in layers]
    gaps_by_spoke = [[radii[layer][spoke] - radii[layer + 1][spoke] for layer in range(UPDATES)] for spoke in range(RAY_COUNT)]
    q = abs((1 - T) + T * mp.e ** (2j * mp.pi / n))
    q = mp.mpf(q)
    normalized_by_spoke = [[gap / q**layer for layer, gap in enumerate(gaps)] for gaps in gaps_by_spoke]
    pooled_gaps = [gap for gaps in gaps_by_spoke for gap in gaps]
    pooled_normalized = [gap for gaps in normalized_by_spoke for gap in gaps]
    layer_envelope = [
        {"layer": layer, "min": fmt(min(values)), "max": fmt(max(values)), "width": fmt(max(values) - min(values))}
        for layer, values in enumerate(radii)
    ]
    spokes = []
    for spoke, gaps in enumerate(gaps_by_spoke):
        telescoping = sum(gaps, mp.mpf(0))
        spokes.append(
            {
                "spoke": spoke + 1,
                "angle_radians": fmt(RAY_ANGLES[spoke]),
                "radii": [fmt(value) for value in (row[spoke] for row in radii)],
                "gaps": [fmt(value) for value in gaps],
                "qk_normalized_gaps": [fmt(value) for value in normalized_by_spoke[spoke]],
                "raw_gap_summary": summary(gaps),
                "qk_normalized_gap_summary": summary(normalized_by_spoke[spoke]),
                "telescoping": {
                    "sum_gaps": fmt(telescoping),
                    "r0_minus_r100": fmt(radii[0][spoke] - radii[-1][spoke]),
                    "residual": fmt(telescoping - (radii[0][spoke] - radii[-1][spoke])),
                },
                "gap_zeta": zeta_comparison(gaps, q),
            }
        )
    return {
        "n": n,
        "updates": UPDATES,
        "t": fmt(T),
        "initial_circumradius_R0": "1",
        "q_vertex_contraction": fmt(q),
        "rays": RAY_COUNT,
        "ray_symmetry_observation": (
            "All eight fixed spokes have equal radii and gaps for n=8 because the candidate remains an "
            "eightfold regular polygon under the circulant update; this is geometric symmetry, not an "
            "inference that eight spokes define the model."
            if n == 8
            else "The eight fixed spokes are a common measurement family; n=12 is not eightfold symmetric, so spoke radii and gaps retain their differences."
        ),
        "layers": [
            {
                "layer": layer,
                "vertices": [[fmt(x), fmt(y)] for x, y in polygon],
                "radii_by_spoke": [fmt(value) for value in radii[layer]],
            }
            for layer, polygon in enumerate(layers)
        ],
        "geometric_envelope": layer_envelope,
        "spokes": spokes,
        "pooled_raw_gap_summary": summary(pooled_gaps, gaps_by_spoke),
        "pooled_qk_normalized_gap_summary": summary(pooled_normalized, normalized_by_spoke),
        "pooled_lag1_scope": "within-spoke adjacent pairs only; 8 x 99 paired observations, with no last-layer-to-next-spoke joins",
        "all_positive_gaps": all(gap > 0 for gap in pooled_gaps),
        "all_ray_intersections_found": len(pooled_gaps) == RAY_COUNT * UPDATES,
    }


def write_plot(data: dict[str, object]) -> None:
    import matplotlib.pyplot as plt

    figure, axes = plt.subplots(2, 2, figsize=(12, 8), constrained_layout=True)
    for column, key in enumerate(("n8", "n12")):
        case = data["cases"][key]
        layers = [row["layer"] for row in case["geometric_envelope"]]
        lower = [float(row["min"]) for row in case["geometric_envelope"]]
        upper = [float(row["max"]) for row in case["geometric_envelope"]]
        axes[0, column].fill_between(layers, lower, upper, alpha=.2, label="8-spoke envelope")
        axes[0, column].plot(layers, lower, linewidth=1, label="min/max radius")
        axes[0, column].plot(layers, upper, linewidth=1)
        axes[0, column].set_title(f"n={case['n']} layer radii")
        axes[0, column].set_xlabel("layer")
        axes[0, column].set_ylabel("radius / R₀")
        axes[0, column].grid(alpha=.25)
        axes[0, column].legend(fontsize=8)
        for spoke in case["spokes"]:
            gaps = [float(value) for value in spoke["gaps"]]
            axes[1, column].plot(range(UPDATES), gaps, linewidth=.8, alpha=.65)
        first_gaps = [float(value) for value in case["spokes"][0]["gaps"]]
        q = float(case["q_vertex_contraction"])
        axes[1, column].plot(range(UPDATES), [first_gaps[0] * q**k for k in range(UPDATES)], "--", linewidth=1.2, label="g₀qᵏ")
        axes[1, column].set_yscale("log")
        axes[1, column].set_title(f"n={case['n']} positive gaps")
        axes[1, column].set_xlabel("layer k")
        axes[1, column].set_ylabel("gap")
        axes[1, column].grid(alpha=.25)
        axes[1, column].legend(fontsize=8)
    figure.suptitle("Polygon pursuit: fixed-ray layer gaps", fontsize=14)
    figure.savefig(ROOT / "spoke_gap_zeta.png", dpi=160)
    plt.close(figure)


def main() -> None:
    data = {
        "schema": "holonics.spoke-gap-zeta.v1",
        "model": {
            "update": "p_j <- (1-t)p_j + t p_(j+1 mod n)",
            "ray_angles": [fmt(angle) for angle in RAY_ANGLES],
            "ray_count": RAY_COUNT,
            "updates": UPDATES,
            "t": fmt(T),
            "initial_circumradius_R0": "1",
        },
        "cases": {"n8": analyze_case(8), "n12": analyze_case(12)},
        "tail_bound_status": "The reported ideal tails are analytic tails of the comparison sequence g0^s q^(ks), not rigorous outward bounds for the measured polygon sequence.",
        "precision": "mpmath 80 decimal digits; decimal strings retain 50 significant digits; no outward interval claim.",
    }
    (ROOT / "spoke_gap_zeta.json").write_text(json.dumps(data, indent=2) + "\n")
    write_plot(data)
    for key, case in data["cases"].items():
        print(key)
        print("  q =", case["q_vertex_contraction"])
        print("  pooled raw gaps:", case["pooled_raw_gap_summary"])
        print("  pooled q^k-normalized gaps:", case["pooled_qk_normalized_gap_summary"])
        print("  telescoping spoke 1:", case["spokes"][0]["telescoping"])
        print("  zeta s=1 spoke 1:", case["spokes"][0]["gap_zeta"]["1"])
        print("  zeta s=2 spoke 1:", case["spokes"][0]["gap_zeta"]["2"])


if __name__ == "__main__":
    main()
