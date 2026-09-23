#!/usr/bin/env python3
"""Verify the stored exact rational zero-navigation certificate."""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path

from exact_policy import (
    SourceReceiver,
    chord_distance_sq,
    factor_count,
    run_policy,
    segment_error_bound,
    source,
    z,
)


def point(raw: list[str]):
    assert len(raw) == 2
    return z(Q(raw[0]), Q(raw[1]))


def read_region(raw: dict) -> tuple[tuple[Q, Q], list[list[tuple[Q, Q]]], int]:
    low, high = map(Q, raw["y_interval"])
    edges = [[point(p) for p in path] for path in raw["boundary"]]
    assert len(edges) == 4 and all(len(path) >= 2 for path in edges)
    assert all(edges[i][-1] == edges[(i + 1) % 4][0] for i in range(4))
    return (low, high), edges, raw["winding"]


def verify_region(raw: dict, witnesses: set) -> None:
    interval, edges, claimed = read_region(raw)
    for edge in edges:
        for a, b in zip(edge, edge[1:]):
            assert (a, b) in witnesses or (b, a) in witnesses
    receiver = SourceReceiver()
    from exact_policy import Region

    reconstructed = Region(interval[0], interval[1], tuple(edges))
    assert receiver.winding(reconstructed) == claimed
    assert claimed == factor_count(*interval)


def verify_policy(policy: dict) -> None:
    witnesses = set()
    for row in policy["segment_certificates"]:
        a, b = map(point, row["segment"])
        pa, pb = source(a), source(b)
        min_sq = chord_distance_sq(pa, pb)
        error_sq = segment_error_bound(a, b) ** 2
        assert min_sq == Q(row["chord_distance_squared"])
        assert error_sq == Q(row["curve_chord_error_squared_upper"])
        assert min_sq > error_sq
        witnesses.add((a, b))
    assert len(witnesses) == policy["cost"]["accepted_segment_certificates"]
    verify_region(policy["root"], witnesses)
    for cut in policy["cuts"]:
        verify_region(cut["parent"], witnesses)
        lower, upper = cut["children"]
        verify_region(lower, witnesses)
        verify_region(upper, witnesses)
        parent_interval, _, parent_n = read_region(cut["parent"])
        lower_interval, lower_edges, lower_n = read_region(lower)
        upper_interval, upper_edges, upper_n = read_region(upper)
        split = Q(cut["cut"])
        assert lower_interval == (parent_interval[0], split)
        assert upper_interval == (split, parent_interval[1])
        assert parent_n == lower_n + upper_n
        assert lower_edges[2] == list(reversed(upper_edges[0]))
        assert cut["port_pair_cancels"] is True
    for terminal in policy["terminal_regions"]:
        verify_region(terminal, witnesses)
    assert sum(p["winding"] for p in policy["terminal_regions"]) == 2
    assert sorted(p["winding"] for p in policy["terminal_regions"])[-2:] == [1, 1]
    assert policy["cost"]["cuts"] == len(policy["cuts"])
    # Refused-attempt counts are a policy execution trace, not a mathematical
    # boundary certificate. Regenerate the deterministic policy to audit them.
    assert run_policy(policy["policy"]) == policy


def main() -> None:
    path = Path(__file__).with_name("receipt.json")
    receipt = json.loads(path.read_text(encoding="utf-8"))
    assert receipt["schema"] == "holonics.exact-zero-navigation-policy.v1"
    assert {p["policy"] for p in receipt["policies"]} == {
        "fixed_midpoint",
        "generator_height",
    }
    for policy in receipt["policies"]:
        verify_policy(policy)
    print(f"verified {path}")


if __name__ == "__main__":
    main()
