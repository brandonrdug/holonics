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
        assert report["schema"] not in ("holonics.recorded-temporal-action.v3",
                                         "holonics.recorded-temporal-action.v4",
                                         "holonics.recorded-temporal-action.v5")
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


def verify_generated_field(report, observation):
    """Independent two-occurrence receiver: rank-one Hermitian solve and full balls.

    This checks the declared unit junction on the actual predictions, including covariance,
    packed signed128 centers, oriented residual and internal contact. It conducts no native
    operation and assigns no semantics to the coordinate aperture.
    """
    field = observation.get("native_generated_field")
    if field is None:
        assert report["schema"] not in ("holonics.recorded-temporal-action.v4",
                                         "holonics.recorded-temporal-action.v5")
        return None
    n = report["aperture"]["target_complex"]
    dim, grain = 6*n, field["grain"]
    assert field["nodes"] == n and grain == 72
    assert field["occurrence_count"] == 2 and field["linked_occurrences"] == 1
    assert field["empty_exterior_input"] is True
    cycle = observation["actual_condition_current_cycle"]
    predictions = [decimal_vector(cycle[key]["coordinates"]) for key in
                   ("prediction_before_observation", "prediction_after_contact")]
    assert len(field["actual_incoming"]) == len(field["lineages"]) == 2
    for at, (incoming, lineage, expected) in enumerate(zip(
            field["actual_incoming"], field["lineages"], predictions)):
        assert len(incoming) == n
        values = [Q(p[c], p["denominator"]) for p in incoming for c in ("real", "imaginary")]
        assert values == expected
        assert lineage["incoming"] == {"resident_nodes":n}
        assert lineage["occurrence"] == at and lineage["frame"] == 0
        assert lineage["received_from"] == (None if at == 0 else 0)
        assert lineage["predecessor_state"] == (None if at == 0 else 0)
        assert lineage["source_contact"] == (None if at == 0 else "emission")
    supports = observation["temporal_support_external_to_field"]
    for name in ("hidden", "later"):
        assert supports[name] == report[name + "_support"]
    for name, expected in zip(("anticipated", "generated"), predictions):
        carrier = observation["prediction_carriers"][name]
        actual, directions = affine(carrier["reading"]["predecessor_reading"])
        assert not directions and actual == expected
    a, b = predictions
    u0 = [v for i in range(n) for v in (Q(0), Q(0), a[2*i], a[2*i+1])] + [Q(0)]*(2*n)
    u1 = [v for i in range(n) for v in (a[2*i], a[2*i+1], b[2*i], b[2*i+1])] + [Q(0)]*(2*n)
    d = u0[:4*n] + [-v for v in b]
    jd = [v for i in range(3*n) for v in (-d[2*i+1], d[2*i])]
    c = [[d[i]*d[j] + jd[i]*jd[j] for j in range(dim)] for i in range(dim)]
    cov = field["junction_covariance"]
    assert cov["rows"] == 1 and cov["width"] == dim*dim+1 and cov["grain"] == 0
    words = cov["intervals"]
    assert all(lo == hi for lo, hi in words) and words[-1][0] > 0
    cden = words[-1][0]
    assert [[Q(words[i*dim+j][0],cden) for j in range(dim)] for i in range(dim)] == c
    v0 = [2*x for x in u0]
    denom = 1 + norm(d)
    real_part, imaginary_part = dot(d,u1), dot(jd,u1)
    v1 = [2*(u1[i] - (d[i]*real_part + jd[i]*imaginary_part)/denom) for i in range(dim)]
    exact = []
    for u, v, prefix in ((u0,v0,v0),(u1,v1,[x-y for x,y in zip(v0,v1)])):
        exact.append((v,[x-y for x,y in zip(v,u)],[2*x-y for x,y in zip(u,v)],prefix))
    previous_held = [0]*dim
    assert len(field["junction_reports"]) == 2
    for at, packet in enumerate(field["junction_reports"]):
        assert packet["width"] == 12*(dim+1) and packet["rows"] == 1 and packet["grain"] == 0
        wire = packet["intervals"]
        assert len(wire) == packet["width"] and all(lo == hi for lo,hi in wire)
        wide = []
        for i in range(0,len(wire),2):
            value = (wire[i][0] & ((1<<64)-1)) | ((wire[i+1][0] & ((1<<64)-1))<<64)
            wide.append(value-(1<<128) if value >= (1<<127) else value)
        sections = [wide[i*(dim+1):(i+1)*(dim+1)] for i in range(6)]
        for segment, expected in zip(sections[:4], exact[at]):
            center = [Q(x,1<<grain) for x in segment[:-1]]
            radius = Q(segment[-1],1<<grain)
            assert radius >= 0 and norm([x-y for x,y in zip(center,expected)]) <= radius*radius
        u = (u0,u1)[at]
        ugrid = [int(x*(1<<grain)) for x in u]
        error_count = sum(Q(v,1<<grain) != x for v,x in zip(ugrid,u))
        assert sections[4] == ugrid + [error_count]
        cv = c if at else [[Q(0)]*dim for _ in range(dim)]
        den = cden if at else 1
        vg = sections[0][:-1]
        residual = [sum(cv[i][j]*den*vg[j] for j in range(dim)) + den*vg[i]
                    - 2*den*(ugrid[i]+previous_held[i]) for i in range(dim)]
        assert sections[5] == residual + [den]
        previous_held = sections[2][:-1]
    internal = field["internal_currents"]
    assert len(internal) == 1
    current = internal[0]
    assert current["source_occurrence"] == 0 and current["receiving_occurrence"] == 1
    assert [native_fraction(p[c]) for p in current["contact"] for c in ("real","imaginary")] == d
    assert native_fraction(current["current"]["real"]) == dot(d,v1)
    assert native_fraction(current["current"]["imaginary"]) == dot(jd,v1)
    stage = report["stages"]["native_generated_field_recurrence"]
    assert stage["deeds"] == 2 and stage["ingress_octets"] == 8
    return {"verified":True,"occurrences":2,"linked_contacts":1,
            "full_covariance_and_oriented_residual":True,"all_four_current_balls_contain_exact_solve":True,
            "exact_internal_current":True,"native_input_matches_retained_predictions":True}


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


RESIDENT_SECTION_REST_MAGIC = b"HRSRST\0\x01"
PCM_DIVISOR = 32768


def resident_point(path, width):
    """Decode one canonical ResidentSectionRest point without invoking native code."""
    data = path.read_bytes()
    assert len(data) >= 40 and data[:8] == RESIDENT_SECTION_REST_MAGIC
    rows, stored_width, grain, bound, population = struct.unpack_from("<QQIIQ", data, 8)
    assert rows == 1 and stored_width == width and population == width
    assert grain == 0 and bound == 64
    assert len(data) == 40 + 16 * population
    intervals = [struct.unpack_from("<qq", data, 40 + 16 * i)
                 for i in range(population)]
    assert all(lo == hi for lo, hi in intervals)
    denominator = intervals[-1][0]
    assert denominator > 0
    coordinates = [Q(lo, denominator) for lo, _ in intervals[:-1]]
    return coordinates, {"rows": rows, "width": stored_width, "grain": grain,
                         "bound_octaves": bound, "population": population}


def read_stereo_pcm16(path):
    with wave.open(str(path), "rb") as recording:
        assert recording.getnchannels() == 2 and recording.getsampwidth() == 2
        rate = recording.getframerate()
        frames = recording.getnframes()
        raw = recording.readframes(frames)
    samples = struct.unpack(f"<{2 * frames}h", raw)
    return rate, frames, samples


def toward_zero(value):
    return value.numerator // value.denominator if value >= 0 else \
        -((-value.numerator) // value.denominator)


def verify_whole_recording(report, observation, source_samples, source_rate):
    """Verify v5's full-recording temporal projections as cold exact receiver checks."""
    whole = report.get("whole_recording")
    if whole is None:
        assert report["schema"] != "holonics.recorded-temporal-action.v5"
        return None

    count = len(source_samples)
    output_frames = count + 1
    assert whole["source_raw_extent"] == count
    assert whole["response_raw_extent"] == 2
    assert whole["output_raw_extent"] == output_frames
    assert whole["gain"] == "8192"
    assert whole["channel_interpretation"] == "real-left-imaginary-right"
    for stage_name in ("whole_recording_initial_condition",
                       "whole_recording_successor_condition"):
        stage = report["stages"][stage_name]
        assert stage["section_readouts"] == 0
        assert stage["numerical_egress_octets"] == 0
    terminal = report["stages"]["whole_recording_terminal_receiver"]
    assert terminal["section_readouts"] == 2
    assert terminal["numerical_egress_octets"] == 2 * (2 * output_frames + 1) * 16

    source = [q for sample in source_samples
              for q in (Q(sample, PCM_DIVISOR), Q(0))]
    cycle = observation["actual_condition_current_cycle"]
    result = {}
    for name, contact_name in (("initial_condition", "free_contact"),
                               ("successor_condition", "identified_contact")):
        projection = whole[name]
        expected_metadata = {
            "receiver": 5,
            "origin": "0",
            "sample_step": f"1/{source_rate}",
            "sample_rate": source_rate,
            "frames": output_frames,
        }
        for field, expected in expected_metadata.items():
            assert projection[field] == expected
        assert projection["lineage"] == (110 if name == "initial_condition" else 111)
        assert isinstance(projection["clipped_sample_population"], int)
        section_path = Path(projection["section_path"])
        wav_path = Path(projection["wav_path"])
        assert section_path.is_absolute() and wav_path.is_absolute()
        section_bytes = section_path.read_bytes()
        wav_bytes = wav_path.read_bytes()
        section_sha256 = hashlib.sha256(section_bytes).hexdigest()
        wav_sha256 = hashlib.sha256(wav_bytes).hexdigest()
        assert section_sha256 == projection["section_sha256"]
        assert wav_sha256 == projection["wav_sha256"]

        condition = vector(cycle[contact_name]["successor"])
        assert len(condition) == 4
        expected = convolve(source, condition)
        coordinates, section_metadata = resident_point(section_path, 2 * output_frames + 1)
        assert coordinates == expected

        rate, frames, pcm = read_stereo_pcm16(wav_path)
        assert rate == source_rate and frames == output_frames
        clipped = 0
        for carrier, (left, right) in zip(zip(coordinates[::2], coordinates[1::2]),
                                           zip(pcm[::2], pcm[1::2])):
            for value, sample in zip(carrier, (left, right)):
                scaled = value * 8192
                unbounded = toward_zero(scaled)
                bounded = max(-32768, min(32767, unbounded))
                assert sample == bounded
                clipped += int(unbounded != bounded)
                remainder = scaled - Q(sample)
                assert (Q(sample) + remainder) / 8192 == value
        assert clipped == projection["clipped_sample_population"]
        result[name] = {
            "verified": True,
            "condition_contact": contact_name,
            "frames": frames,
            "clipped_sample_population": clipped,
            "section_sha256": section_sha256,
            "wav_sha256": wav_sha256,
            "section": section_metadata,
            "full_real_pcm_convolution_matches": True,
            "fixed_gain_pcm_and_remainders_reconstruct": True,
        }
    return {"verified": True, "source_frames": count, "output_frames": output_frames,
            "source_sample_rate": source_rate, "initial_condition": result["initial_condition"],
            "successor_condition": result["successor_condition"],
            "zero_egress_stages": True}


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
    generated_field = verify_generated_field(report, observation)
    whole_recording = verify_whole_recording(report, observation, samples, rate)
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
        if name not in ("terminal_observer", "whole_recording_terminal_receiver"):
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
        "condition_current_cycle":condition_current_cycle,"generated_field":generated_field,
        "whole_recording":whole_recording}


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
