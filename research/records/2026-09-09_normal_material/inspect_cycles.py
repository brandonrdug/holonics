"""Exact cold measurements of a declared observed period; never a native stopping rule.

Usage: python inspect_cycles.py PRIVATE_REPORT.json NEW_RECEIPT.json --period N
The complete junction source and outgoing balls are compared, not only emitted bytes.
"""
import argparse
import json
import runpy
from fractions import Fraction as Q
from pathlib import Path

decoder = runpy.run_path(str(Path(__file__).with_name("inspect_feedback.py")))


def difference(a, b):
    center = [x - y for x, y in zip(a[0], b[0])]
    radius = a[1] + b[1]
    square = sum(x * x for x in center)
    cross_upper = 2 * sum(map(abs, center)) * radius
    return {
        "nominal_squared_norm": square,
        "lower_squared_norm": max(Q(0), square - cross_upper),
        "upper_squared_norm": square + cross_upper + radius * radius,
        "joint_radius": radius,
    }


def inspect(document, period):
    assert period > 0
    generation = document["generation"]
    entries = document["emission_current_history"]
    roots = len(document["body"]["lineage"][generation["native_from"]]["incoming"])
    decode = decoder["junction_ball"]
    parts = decoder["JunctionPart"]
    outgoing = [decode(e, document["fractional_bits"], roots, parts.OUTGOING) for e in entries]
    source = [decode(e, document["fractional_bits"], roots, parts.SOURCE) for e in entries]
    selected = [r["native"]["selected"] for r in generation["readings"]]
    count = len(entries)
    starts = [start for start in range(count - 2 * period + 1)
              if all(selected[i] == selected[i + period] and source[i] == source[i + period]
                     for i in range(start, count - period))]
    start = min(starts) if starts else None
    returned = {
        "declared_period": period,
        "readings": count,
        "periodic_source_and_face_start": start,
        "generation_disposition": generation["disposition"],
        "rows": [],
    }
    if start is None:
        return returned
    differences = [difference(outgoing[i + period], outgoing[i])
                   for i in range(start, count - period)]
    decreases = [differences[i + period]["upper_squared_norm"]
                 < differences[i]["lower_squared_norm"]
                 for i in range(len(differences) - period)]
    returned["successive_period_comparisons"] = len(decreases)
    returned["certified_strict_decreases"] = sum(decreases)
    returned["all_period_differences_exclude_zero"] = all(
        row["lower_squared_norm"] > 0 for row in differences)
    for i, row in enumerate(differences):
        returned["rows"].append({
            "occurrence": entries[start + i]["occurrence"],
            "later_occurrence": entries[start + i + period]["occurrence"],
            "selected_coordinate": selected[start + i],
            **{key: str(value) for key, value in row.items()},
        })
    return returned


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--period", type=int, required=True)
    args = parser.parse_args()
    document = json.loads(args.report.read_text())
    result = {
        "grade": "established-bounded",
        "evidence": ["measured", "computational-witness"],
        "scope": "Finite recorded source/outgoing enclosures. No infinite-cycle, complete-state "
                 "convergence or physical-energy claim. No model operation is run.",
        "native_development_until": document["development_native_until"],
        "measurement": inspect(document, args.period),
    }
    with args.receipt.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
