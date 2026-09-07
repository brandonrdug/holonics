#!/usr/bin/env python3
"""Cold independent Fraction/PCM comparison; never supplies a target to native development."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import struct
import wave


def coordinates(point):
    pairs = point["raw_words"]
    assert all(a == b for a, b in pairs)
    den = pairs[-1][0]
    assert den > 0
    actual = [Q(a, den) for a, _ in pairs[:-1]]
    assert actual == [Q(value) for value in point["coordinates"]]
    return actual


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
        # The report's rational clocks use the repository BigRational serializer. Their sample
        # support is independently checked against the unchanged source PCM and exact rate.
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
    for name, stage in report["stages"].items():
        if name != "terminal_observer":
            assert stage["section_readouts"] == 0 and stage["numerical_egress_octets"] == 0
    return {"report":str(path),"source_sha256":source["sha256"],"sample_rate":rate,
        "pcm_support_and_two_native_convolutions_agree":True,
        "native_preimage_status":preimage["status"],"condition_direction_count":len(directions),
        "native_prediction_status":observation["prediction"]["status"],
        "cold_later_image_directions":[[str(q) for q in row] for row in later_directions],
        "cold_later_image_is_singleton":not any(any(row) for row in later_directions),
        "native_stages_have_zero_numerical_readouts":True}


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
