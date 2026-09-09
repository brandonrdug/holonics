"""Compare recorded actuation realizations through exact packet and current receivers.

Usage: python inspect_phase_comparison.py BASELINE.json INTERVENTION.json NEW_RECEIPT.json
No model operation, phase choice or text selection is performed here.
"""
import json
import runpy
import sys
from fractions import Fraction as Q
from pathlib import Path

decoder = runpy.run_path(str(Path(__file__).with_name("inspect_feedback.py")))


def multiply(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def packet(input, width):
    amplitude = Q(1), Q(0)
    coordinate = 0
    place = 1
    for start in range(0, len(input), width):
        nonzero = []
        for index, v in enumerate(input[start:start + width]):
            value = Q(v["real"], v["denominator"]), Q(v["imaginary"], v["denominator"])
            if value != (0, 0):
                assert sum(x * x for x in value) == 1
                nonzero.append((index, value))
        assert len(nonzero) == 1
        index, value = nonzero[0]
        coordinate += place * index
        place *= width
        amplitude = multiply(amplitude, value)
    return coordinate, amplitude


def inspect(left, right):
    a, b = left["generation"], right["generation"]
    la = left["body"]["lineage"][a["native_from"]:a["native_until"]]
    lb = right["body"]["lineage"][b["native_from"]:b["native_until"]]
    count = min(len(la), len(lb))
    width = right["material_target"]["factor_width"]
    pairs = [(packet(x["incoming"], width), packet(y["incoming"], width))
             for x, y in zip(la, lb)]
    outgoing = decoder["outgoing"]
    separated = equal = 0
    witness = None
    for x, y in zip(left["emission_current_history"], right["emission_current_history"]):
        ca, ra = outgoing(x, left["fractional_bits"], len(la[0]["incoming"]))
        cb, rb = outgoing(y, right["fractional_bits"], len(lb[0]["incoming"]))
        distance = sum((u - v) ** 2 for u, v in zip(ca, cb))
        equal += int(ca == cb and ra == rb)
        if distance > (ra + rb) ** 2:
            separated += 1
            if witness is None:
                witness = {"baseline_occurrence": x["occurrence"],
                           "intervention_occurrence": y["occurrence"],
                           "squared_center_distance": str(distance),
                           "squared_sum_of_radii": str((ra + rb) ** 2)}
    return {
        "matched_actuations": count,
        "same_complete_tensor_inputs": sum(x == y for x, y in pairs),
        "different_root_inputs": sum(x["incoming"] != y["incoming"] for x, y in zip(la, lb)),
        "same_emitted_octets": a["emitted_octets"] == b["emitted_octets"],
        "identical_outgoing_balls": equal,
        "disjoint_outgoing_balls": separated,
        "first_separating_witness": witness,
        "same_material_operator": left["body"]["material_transport"] == right["body"]["material_transport"],
        "same_contact_map": left["body"]["operative_contacts"]["contacts"] == right["body"]["operative_contacts"]["contacts"],
        "intervention": right.get("actuation_phase_pairs", right.get("actuation_phase_pair")),
        "factor_phases": right["actuation_factor_phases"],
        "emitted_octets": b["emitted_octets"],
        "disposition": b["disposition"],
    }


def main():
    baseline, intervention, destination = map(Path, sys.argv[1:])
    result = {"grade": "established-bounded", "evidence": ["measured", "computational-witness"],
              "scope": "Matched stored-model study with distinct actuation histories. Equality is "
                       "at the declared tensor/word receivers, not source identity or universal future agreement.",
              "comparison": inspect(json.loads(baseline.read_text()), json.loads(intervention.read_text()))}
    with destination.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
