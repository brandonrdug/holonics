"""Cold comparison of recorded receivers; no model execution or learning.

Usage: python inspect_feedback.py PRIVATE_FALSE.json PRIVATE_TRUE.json NEW_RECEIPT.json
The junction wire decoder follows field/junction/enclosure.rs::decode_report.
Only derived current comparisons and the already reported failed output are exported.
"""
import json
import sys
from enum import IntEnum
from fractions import Fraction as Q
from pathlib import Path


class JunctionPart(IntEnum):
    POTENTIAL = 0
    OUTGOING = 1
    HELD = 2
    POTENTIAL_PREFIX = 3
    SOURCE = 4


def junction_ball(entry, grain, roots, part):
    words = entry["junction"]["intervals"]
    width = 6 * roots
    stride = width + 1
    assert len(words) == 12 * stride and all(a == b for a, b in words)

    def value(i):
        raw = (words[2 * i][0] & ((1 << 64) - 1)) | (
            (words[2 * i + 1][0] & ((1 << 64) - 1)) << 64
        )
        return Q(raw - (1 << 128) if raw >= (1 << 127) else raw, 1 << grain)

    center = [value(part * stride + j) for j in range(width)]
    radius = value(part * stride + width)
    assert radius >= 0
    return center, radius


def outgoing(entry, grain, roots):
    return junction_ball(entry, grain, roots, JunctionPart.OUTGOING)


def inspect(document):
    generation = document["generation"]
    entries = document["emission_current_history"]
    lineage = document["body"]["lineage"][
        generation["native_from"] : generation["native_until"]
    ]
    roots = len(lineage[0]["incoming"])
    balls = [outgoing(e, document["fractional_bits"], roots) for e in entries]
    # Four is the observed byte period of this recorded " the" face, not a native governor.
    lag = 4
    compared = unequal = separated = 0
    witness = None
    for i in range(4, len(entries) - lag):
        code = generation["readings"][i]["native"]["selected"]
        if code != generation["readings"][i + lag]["native"]["selected"]:
            continue
        a, ra = balls[i]
        b, rb = balls[i + lag]
        distance = sum((x - y) ** 2 for x, y in zip(a, b))
        disjoint = distance > (ra + rb) ** 2
        compared += 1
        unequal += int(a != b)
        separated += int(disjoint)
        if disjoint and witness is None:
            witness = {
                "first_occurrence": entries[i]["occurrence"],
                "later_occurrence": entries[i + lag]["occurrence"],
                "selected_coordinate": code,
                "outgoing_center_square_distance": str(distance),
                "sum_radii_squared": str((ra + rb) ** 2),
            }
    inputs = {
        sum(Q(v["real"] ** 2 + v["imaginary"] ** 2, v["denominator"] ** 2)
            for v in event["incoming"])
        for event in lineage
    }
    return {
        "prompt_contact_response": document["contact_response_during_prompt"],
        "prompt_contact_deposits": document["prompt_operative_returns"]
        - document["development_operative_returns"],
        "prompt_and_emission_wall_seconds": document["prompt_and_emission_wall_seconds"],
        "generation_from": generation["native_from"],
        "generation_until": generation["native_until"],
        "disposition": generation["disposition"],
        "output": document["utf8"],
        "observed_byte_lag": lag,
        "same_selected_coordinate_comparisons": compared,
        "unequal_outgoing_centers": unequal,
        "disjoint_outgoing_balls": separated,
        "separating_witness": witness,
        "exterior_input_norm_squares": sorted(map(str, inputs)),
        "every_generated_source_is_material_actuation": all(
            "material-actuation" in event["source_contact"] for event in lineage
        ),
    }


def main():
    first, second, destination = map(Path, sys.argv[1:])
    documents = [json.loads(p.read_text()) for p in (first, second)]
    receipt = {
        "grade": "established-bounded",
        "evidence": ["measured", "computational-witness"],
        "scope": "Two saved-model prompt continuations; exact cold wire arithmetic. "
        "Unit-chart input norm is not calibrated physical energy. Equal text is not "
        "complete-state equality. No arbitrary-period or asymptotic claim.",
        "same_output": documents[0]["utf8"] == documents[1]["utf8"],
        "same_complete_reported_body": documents[0]["body"] == documents[1]["body"],
        "runs": [inspect(d) for d in documents],
    }
    with destination.open("x") as out:
        json.dump(receipt, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
