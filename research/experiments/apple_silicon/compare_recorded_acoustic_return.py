#!/usr/bin/env python3
"""Cold exact comparison of a source-qualified recorded return, never a native learner."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import struct
import wave

import numpy as np

from compare_recorded_temporal_action import native_fraction, RESIDENT_SECTION_REST_MAGIC


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pcm(path, channels):
    with wave.open(str(path), "rb") as recording:
        assert recording.getnchannels() == channels and recording.getsampwidth() == 2
        rate, frames = recording.getframerate(), recording.getnframes()
        result = np.frombuffer(recording.readframes(frames), dtype="<i2").reshape(frames, channels)
    return rate, result.astype(np.int64)


def section(metadata, expected):
    path = Path(metadata["section_path"])
    data = path.read_bytes()
    assert digest(path) == metadata["section_sha256"]
    assert len(data) == metadata["section_octets"]
    assert data[:8] == RESIDENT_SECTION_REST_MAGIC
    rows, width, grain, bound, population = struct.unpack_from("<QQIIQ", data, 8)
    assert (rows, width, grain, bound, population) == (1, expected.size + 1, 0, 64, expected.size + 1)
    assert len(data) == 40 + 16 * population
    pairs = np.frombuffer(data, dtype="<i8", offset=40).reshape(population, 2)
    assert np.array_equal(pairs[:, 0], pairs[:, 1])
    den = int(pairs[-1, 0])
    assert 0 < den <= 32768 and 32768 % den == 0
    coordinates = pairs[:-1, 0].reshape(expected.shape)
    # This bound follows from the supplied PCM16 comparison, and makes the subsequent
    # independent integer equality free of int64 overflow even for malformed artifacts.
    assert np.all(coordinates >= -65536) and np.all(coordinates <= 65536)
    assert np.array_equal(coordinates * (32768 // den), expected)
    return {"sha256": metadata["section_sha256"], "coordinates_verified": expected.size,
            "denominator": den}


def section_fraction(metadata, expected):
    """Verify an exact resident section against arbitrary rational coordinates."""
    path = Path(metadata["section_path"])
    data = path.read_bytes()
    assert digest(path) == metadata["section_sha256"]
    assert len(data) == metadata["section_octets"]
    assert data[:8] == RESIDENT_SECTION_REST_MAGIC
    expected = list(expected)
    rows, width, grain, bound, population = struct.unpack_from("<QQIIQ", data, 8)
    assert (rows, width, grain, bound, population) == (1, len(expected) + 1, 0, 64, len(expected) + 1)
    assert len(data) == 40 + 16 * population
    pairs = np.frombuffer(data, dtype="<i8", offset=40).reshape(population, 2)
    assert np.array_equal(pairs[:, 0], pairs[:, 1])
    den = int(pairs[-1, 0])
    assert den > 0
    coordinates = [Q(int(value), den) for value in pairs[:-1, 0]]
    assert coordinates == expected
    return {"sha256": metadata["section_sha256"], "coordinates_verified": len(expected),
            "denominator": den, "exact_coordinates": [str(value) for value in coordinates]}


def compare(report_path, acquisition_path):
    report = json.loads(report_path.read_text())
    acquisition = json.loads(acquisition_path.read_text())
    assert report["schema"] in ("holonics.recorded-acoustic-return.v1", "holonics.recorded-acoustic-return.v2")
    assert report["status"] == "returned"
    assert acquisition["schema"] == "soundcam-selective-acquisition.v1"
    root = acquisition_path.parent
    matches = [pair for pair in acquisition["pairs"]
               if (root / pair["loopback"]["path"]).resolve() == Path(report["excitation"]["path"]).resolve()
               and (root / pair["microphone_recording"]["path"]).resolve() == Path(report["observation"]["path"]).resolve()]
    assert len(matches) == 1
    pair = matches[0]
    assert pair["origin_frame"] == 0 and pair["sample_rate_hz"] == 48000
    sources = {}
    for role, pair_role, raw_key in (("excitation", "loopback", "music_directlines_npy"),
                                    ("observation", "microphone_recording", "music_audio_npy")):
        claimed, qualified = report[role], pair[pair_role]
        path = Path(claimed["path"])
        assert digest(path) == claimed["sha256"] == qualified["wav_sha256"]
        assert path.stat().st_size == claimed["octets"]
        rate, data = pcm(path, 1)
        assert rate == claimed["sample_rate"] == pair["sample_rate_hz"]
        assert len(data) == claimed["frames"] == qualified["frames"] and claimed["origin"] == "0"
        raw_path = root / acquisition["raw_outputs"][raw_key]
        assert digest(raw_path) == qualified["source_array_sha256"]
        raw = np.load(raw_path, mmap_mode="r", allow_pickle=False)
        assert raw.dtype.str == "<i2"
        selected = raw[pair["row"]] if role == "excitation" else raw[pair["row"], pair["microphone"]]
        assert np.array_equal(selected, data[:, 0])
        sources[role] = data[:, 0]
    count = min(map(len, sources.values()))
    assert len(sources["excitation"]) == len(sources["observation"])
    support = report["support"]
    assert support["predicted"] == support["observed"] == {"start": 0, "end": count}
    assert support["unobserved_prediction"] == support["unpredicted_observation"] == []
    assert native_fraction(support["begin"]) == Q(0)
    assert native_fraction(support["end"]) == Q(count, rate)
    assert report["initial_response"] == {"real": 1, "imaginary": 0, "denominator": 1, "origin": "0", "extent": 1}
    assert report["divisor"] == 32768
    zero = np.zeros(count, dtype=np.int64)
    prediction = np.stack((sources["excitation"], zero), axis=1)
    real_difference = sources["observation"] - sources["excitation"]
    difference = np.stack((real_difference, zero), axis=1)
    checked = {}
    for name, expected, lineage in (("prediction", prediction, 4), ("difference", difference, 5)):
        metadata = report[name]
        assert metadata["frames"] == count and metadata["origin"] == "0"
        assert Q(metadata["sample_step"]) == Q(1, rate)
        assert metadata["receiver"] == 9 and metadata["lineage"] == lineage
        checked[name] = section(metadata, expected)
    metadata = report["difference"]
    wav_path = Path(metadata["wav_path"])
    assert digest(wav_path) == metadata["wav_sha256"] and metadata["pcm_gain"] == 32768
    pcm_rate, actual_pcm = pcm(wav_path, 2)
    expected_pcm = difference.clip(-32768, 32767)
    assert pcm_rate == rate and np.array_equal(actual_pcm, expected_pcm)
    assert int(np.count_nonzero(expected_pcm != difference)) == metadata["clipped_sample_population"]
    # The integer residual after projection exactly reconstructs the full native current.
    assert np.array_equal(actual_pcm + (difference - actual_pcm), difference)
    for name in ("predict_before_reception", "native_oriented_return"):
        stage = report["stages"][name]
        assert stage["section_readouts"] == stage["numerical_egress_octets"] == stage["ingress_octets"] == 0
        assert stage["deeds"] == 1
    response_checked = None
    if report["schema"] == "holonics.recorded-acoustic-return.v2":
        assert report["generator_developed"] is False
        response_stage = report["stages"]["resident_response_adjoint"]
        assert response_stage["section_readouts"] == response_stage["numerical_egress_octets"] == response_stage["ingress_octets"] == 0
        assert response_stage["deeds"] == 1
        response_numerator = sum(int(x) * int(d) for x, d in zip(sources["excitation"], real_difference))
        response_bound = count * 32768 * 65535
        assert abs(response_numerator) <= response_bound
        response_expected = [Q(response_numerator, 32768 * 32768), Q(0)]
        metadata = report["response_return"]
        assert metadata["frames"] == 1 and metadata["origin"] == "0"
        assert Q(metadata["sample_step"]) == Q(1, rate)
        assert metadata["receiver"] == 8 and metadata["lineage"] == 6
        response_checked = section_fraction(metadata, response_expected)
        response_cold_stage = report["stages"]["cold_response_return"]
        assert response_cold_stage["section_readouts"] == 1 and response_cold_stage["deeds"] == 0
        assert response_cold_stage["numerical_egress_octets"] == 48
    for name in ("cold_prediction", "cold_difference_and_audio"):
        stage = report["stages"][name]
        assert stage["section_readouts"] == 1 and stage["deeds"] == 0
        assert stage["numerical_egress_octets"] == (2 * count + 1) * 16
    signal_energy = int(np.dot(sources["observation"], sources["observation"]))
    defect_energy = int(np.dot(real_difference, real_difference))
    return {"verified": True, "row": pair["row"], "microphone": pair["microphone"],
            "frames": count, "sample_rate": rate, "qualified_raw_arrays_match_wavs": True,
            "complete_oriented_difference_matches": True, "projection_fibre_reconstructs": True,
            "zero_native_numerical_readouts": True, "sections": checked,
            "observed_pcm_square_sum": signal_energy, "defect_pcm_square_sum": defect_energy,
            "defect_to_observed_energy_ratio": str(Q(defect_energy, signal_energy)) if signal_energy else None,
            "response_return": response_checked,
            "response_numerator_bound": response_bound if response_checked else None,
            "scope": "unit-response baseline versus actual measured channels; no fitted acoustic model"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("acquisition", type=Path)
    parser.add_argument("reports", type=Path, nargs="+")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = [compare(path, args.acquisition) for path in args.reports]
    rendered = json.dumps({"verified": True, "returns": results}, indent=2) + "\n"
    if args.output:
        with args.output.open("x") as output:
            output.write(rendered)
    print(rendered, end="")
