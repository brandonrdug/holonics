#!/usr/bin/env python3
"""Cold independent Fraction/PCM comparison; never supplies a target to native development."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import struct
import wave


def native_fraction(value):
    def integer(parts):
        sign, limbs = parts
        return sign * sum(limb << (32*i) for i, limb in enumerate(limbs))
    numerator, denominator = value
    return Q(integer(numerator), integer(denominator))


def affine(reading):
    if "Unique" in reading:
        return [native_fraction(v) for v in reading["Unique"]["current"]], []
    reading = reading["Plural"]
    return ([native_fraction(v) for v in reading["particular"]],
            [[native_fraction(v) for v in row] for row in reading["directions"]])


def coordinates(point):
    pairs = point["raw_words"]
    assert all(a == b for a, b in pairs)
    den = pairs[-1][0]
    assert den > 0
    actual = [Q(a, den) for a, _ in pairs[:-1]]
    assert actual == [Q(value) for value in point["coordinates"]]
    return actual


def vector(values):
    return [native_fraction(value) for value in values]


def decimal_vector(values):
    return [Q(value) for value in values]


def norm(values):
    return sum((value * value for value in values), Q(0))


def dot(left, right):
    assert len(left) == len(right)
    return sum((a * b for a, b in zip(left, right)), Q(0))


def contact_vectors(contact):
    return {name: vector(contact[name]) for name in
            ("predecessor", "successor", "incoming_normal", "returned_normal", "difference")}


def verify_condition_current_cycle(report, observation, source_inputs, directions):
    """Verify the v3 retained-current cycle from cold exact Fraction data.

    The cycle is optional so reports produced by the v1/v2 examples retain their prior scope.
    Every check here compares serialized native Rat values with an independently recomputed
    exact convolution or metric identity; no condition is selected from a fibre.
    """
    cycle = observation.get("actual_condition_current_cycle")
    if cycle is None:
        assert report["schema"] != "holonics.recorded-temporal-action.v3"
        return None

    initial = coordinates(cycle["initial_condition"])
    expected_initial = [Q(1), Q(0), Q(0), Q(0)]
    assert initial == expected_initial
    if "training_controls" in report:
        controls = report["training_controls"]
        assert len(controls) > 1 and controls[1] == [1, 0, 0, 0]

    def check_contact(contact, *, predecessor=None, successor=None, zero_difference=False):
        assert contact["metric"] == "UnitAdmittanceRealification"
        assert contact["status"] == "Compatible"
        values = contact_vectors(contact)
        assert all(len(row) == len(initial) for row in values.values())
        if predecessor is not None:
            assert values["predecessor"] == predecessor
        if successor is not None:
            assert values["successor"] == successor
        if zero_difference:
            assert not any(values["difference"])
        assert norm(values["predecessor"]) + norm(values["incoming_normal"]) == \
            norm(values["successor"]) + norm(values["returned_normal"])
        assert all(values["successor"][i] - values["predecessor"][i] == values["difference"][i]
                   for i in range(len(values["difference"])))
        assert all(values["incoming_normal"][i] - values["returned_normal"][i] == values["difference"][i]
                   for i in range(len(values["difference"])))
        return values

    free = check_contact(cycle["free_contact"], predecessor=initial,
                         successor=initial, zero_difference=True)
    assert not any(free["incoming_normal"]) and not any(free["returned_normal"])
    identified = check_contact(cycle["identified_contact"], predecessor=initial)
    assert cycle["free_contact"]["contact"] == 1
    assert cycle["identified_contact"]["contact"] == 2
    assert cycle["contacts"] == 2
    assert cycle.get("before_relation_cut", -1) >= 0
    assert cycle.get("after_relation_cut", -1) == cycle["before_relation_cut"] + 1
    assert cycle["identified_contact"]["relation_cut"] == report["preimage_relation_cut"]

    hidden = source_inputs["hidden"]
    later = source_inputs["later"]
    hidden_actual = coordinates(observation["hidden_actual"])
    later_actual = coordinates(observation["later_actual"])
    prediction_before = cycle["prediction_before_observation"]
    prediction_after = cycle["prediction_after_contact"]
    assert prediction_before["status"] == "unique"
    assert prediction_after["status"] == "unique"
    assert decimal_vector(prediction_before["coordinates"]) == convolve(hidden, initial)
    assert decimal_vector(prediction_after["coordinates"]) == convolve(later, identified["successor"])
    assert convolve(hidden, initial) == convolve(hidden, free["successor"])
    assert convolve(hidden, identified["successor"]) == hidden_actual
    assert convolve(later, identified["successor"]) == later_actual
    assert all(dot(identified["difference"], direction) == Q(0)
               for direction in directions)

    return {
        "verified": True,
        "contacts": cycle["contacts"],
        "before_relation_cut": cycle["before_relation_cut"],
        "after_relation_cut": cycle["after_relation_cut"],
        "preimage_direction_count": len(directions),
        "free_successor_is_initial": free["successor"] == initial,
        "identified_successor_hidden_convolution": True,
        "identified_difference_orthogonal_to_preimage": True,
        "before_prediction_initial_law": True,
        "after_prediction_later_law": True,
    }


def convolve(source, response):
    n, k = len(source) // 2, len(response) // 2
    out = [Q(0) for _ in range(2 * (n + k - 1))]
    for i in range(n):
        for j in range(k):
            ar, ai = source[2*i:2*i+2]
            br, bi = response[2*j:2*j+2]
            out[2*(i+j)] += ar*br - ai*bi
            out[2*(i+j)+1] += ar*bi + ai*br
    return out


def compare(path):
    report = json.loads(path.read_text())
    source = report["source"]
    wav = Path(source["path"])
    assert hashlib.sha256(wav.read_bytes()).hexdigest() == source["sha256"]
    with wave.open(str(wav), "rb") as recording:
        assert recording.getnchannels() == 1 and recording.getsampwidth() == 2
        rate = recording.getframerate()
        assert rate == source["sample_rate"]
        count = recording.getnframes()
        assert count == source["samples"]
        samples = struct.unpack(f"<{count}h", recording.readframes(count))
    observation = report["observation"]
    response = coordinates(observation["hidden_response"])
    inputs = {}
    for role in ("hidden", "later"):
        support = report[f"{role}_support"]
        start, end = support["coefficient_from"], support["coefficient_until"]
        assert native_fraction(support["begin"]) == Q(start,rate)
        assert native_fraction(support["end"]) == Q(end,rate)
        actual = coordinates(observation[f"{role}_source"])
        expected = [q for sample in samples[start:end] for q in (Q(sample,32768),Q(0))]
        assert actual == expected
        assert end-start == report["aperture"]["source_complex"]
        inputs[role] = actual
        assert coordinates(observation[f"{role}_actual"]) == convolve(actual,response)
    preimage = observation["preimage"]
    particular = [Q(value) for value in preimage["particular"]]
    directions = [[Q(value) for value in row] for row in preimage["directions"]]
    hidden_target = coordinates(observation["hidden_actual"])
    assert convolve(inputs["hidden"],particular) == hidden_target
    assert all(not any(convolve(inputs["hidden"],d)) for d in directions)
    later_directions = [convolve(inputs["later"],d) for d in directions]
    if preimage["status"] == "unique":
        assert not directions and particular == response
        assert observation["prediction"]["status"] == "unique"
        assert [Q(v) for v in observation["prediction"]["coordinates"]] == convolve(inputs["later"],response)
        assert observation["exact_agreement"] is True
    else:
        assert preimage["status"] == "plural" and directions
        assert observation["prediction"]["status"] == "native-consumer-refused"
    condition_current_cycle = verify_condition_current_cycle(
        report, observation, inputs, directions)
    family_verified = False
    if "whole_image" in observation:
        image = observation["whole_image"]
        assert image["coverage"]["kind"] == "complete"
        output, output_directions = affine(image["supported_outputs"])
        assert not output_directions and output == convolve(inputs["later"],response)
        joint, joint_directions = affine(image["joint"])
        assert convolve(inputs["later"],joint[:4]) == joint[4:]
        assert all(convolve(inputs["later"],d[:4]) == d[4:] for d in joint_directions)
        assert coordinates(observation["whole_image_carried"]) == output+[Q(0),Q(0)]
        refined = observation["refined_condition"]["reading"]
        assert refined["kind"] == "compatible"
        base = [native_fraction(v) for v in refined["particular"]]
        assert convolve(inputs["later"],base) == output
        assert all(not any(convolve(inputs["later"],[native_fraction(v) for v in d]))
                   for d in refined["directions"])
        assert report["complete_bounded_comparison"] is True
        family_verified = True
    for name, stage in report["stages"].items():
        if name != "terminal_observer":
            assert stage["section_readouts"] == 0 and stage["numerical_egress_octets"] == 0
    return {"report":str(path),"source_sha256":source["sha256"],"sample_rate":rate,
        "pcm_support_and_two_native_convolutions_agree":True,
        "native_preimage_status":preimage["status"],"condition_direction_count":len(directions),
        "native_prediction_status":observation["prediction"]["status"],
        "cold_later_image_directions":[[str(q) for q in row] for row in later_directions],
        "cold_later_image_is_singleton":not any(any(row) for row in later_directions),
        "native_stages_have_zero_numerical_readouts":True,
        "native_whole_image_continuation_and_refinement_verified":family_verified,
        "condition_current_cycle_verified":None if condition_current_cycle is None else condition_current_cycle["verified"],
        "condition_current_cycle":condition_current_cycle}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", type=Path, nargs="+")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = {"truth_status":"established-bounded","evidence_tags":["measured"],
        "scope":"cold Fraction and original PCM comparison; no native execution or learning",
        "comparisons":[compare(path) for path in args.reports]}
    with args.output.open("x") as output:
        json.dump(result,output,indent=2)
        output.write("\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
