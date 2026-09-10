"""Read completed reports; never execute a model or inspect training passages.

The first transport ball follows NormalLayout/field_normal_material.cuh. Its signed
wide words carry a complex centre plus a joint radius at the report's current grain.
"""
import json
import sys
from pathlib import Path


def inspect(document):
    generation = document["generation"]
    emitted = generation["emitted_octets"]
    witnesses = []
    following_t = {}
    all_margins_separate = True
    for index, (entry, reading) in enumerate(zip(
        document["emission_current_history"], generation["readings"], strict=True
    )):
        packet = reading["native"]
        dimension = packet["target_dimension"]
        words = entry["transport"]["intervals"]
        assert all(low == high for low, high in words)

        def wide(at):
            limb_bits = 64  # serialized i64 limbs of the native i128 report
            mask = (1 << limb_bits) - 1
            value = (words[2 * at][0] & mask) | (
                (words[2 * at + 1][0] & mask) << limb_bits
            )
            width = 2 * limb_bits
            return value - (1 << width) if value >= 1 << (width - 1) else value

        quadrature = {"real": 0, "imaginary": 1}[packet["quadrature"]]
        potentials = [wide(2 * i + quadrature) for i in range(dimension)]
        radius = wide(2 * dimension)
        selected = packet["selected"]
        assert radius >= 0 and packet["unexcluded"] == [selected]
        gap = potentials[selected] - max(v for i, v in enumerate(potentials) if i != selected)
        # Distance to the nearest equal-maximum boundary is gap/sqrt(2).
        separates = gap > 0 and gap * gap > 2 * radius * radius
        all_margins_separate &= separates
        new_after_t = index > 0 and emitted[index - 1] == ord("t") and selected not in following_t
        if new_after_t:
            following_t[selected] = index
        if index == 0 or new_after_t:
            witnesses.append({
                "emission_index": index, "source_occurrence": entry["occurrence"],
                "selected_octet": selected, "previous_emitted_octet": emitted[index - 1] if index else None,
                "gap_grid_numerator": str(gap), "radius_grid_numerator": str(radius),
                "grain": document["fractional_bits"], "strict_maximum_over_full_ball": separates,
            })
    return {
        "output": bytes(emitted).decode("utf8"), "disposition": generation["disposition"],
        "every_recorded_selection_has_separating_margin": all_margins_separate,
        "distinct_next_octets_after_same_emitted_t": sorted(following_t),
        "witnesses": witnesses,
    }


if __name__ == "__main__":
    before, after, destination = map(Path, sys.argv[1:])
    a, b = [json.loads(path.read_text()) for path in (before, after)]
    receipt = {
        "grade": "established-bounded", "evidence": ["computational-witness"],
        "scope": "Cold inspection of two completed live-propagation reports. No source-passage attribution, model run or asymptotic claim.",
        "same_complete_reported_body": a["body"] == b["body"],
        "same_generation": a["generation"] == b["generation"],
        "same_recorded_current_history": a["emission_current_history"] == b["emission_current_history"],
        "prompt_and_emission_seconds": [d["prompt_and_emission_wall_seconds"] for d in (a, b)],
        "feedback": inspect(b),
    }
    with destination.open("x") as output:
        json.dump(receipt, output, indent=2)
        output.write("\n")
