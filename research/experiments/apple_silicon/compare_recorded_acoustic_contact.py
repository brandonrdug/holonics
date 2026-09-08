#!/usr/bin/env python3
"""Cold exact verifier for sequential recorded acoustic temporal contacts.

This observer never launches native work.  It checks source provenance, the resident
ball reports, the retained exact temporal tail, and the cold rational projection derived
from the original PCM16 operands.
"""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import math
from pathlib import Path
import struct
import wave

import numpy as np

from compare_recorded_acoustic_return import RESIDENT_SECTION_REST_MAGIC
from compare_recorded_temporal_action import native_fraction

MASK64 = (1 << 64) - 1
TWO128 = 1 << 128
ZERO = (Q(0), Q(0))


def complex_pair(real=0, imaginary=0):
    return Q(real), Q(imaginary)


def pair_add(left, right):
    return left[0] + right[0], left[1] + right[1]


def pair_sub(left, right):
    return left[0] - right[0], left[1] - right[1]


def pair_scale(value, scalar):
    scalar = Q(scalar)
    return value[0] * scalar, value[1] * scalar


def pair_mul(left, right):
    return (left[0] * right[0] - left[1] * right[1],
            left[0] * right[1] + left[1] * right[0])


class RationalSeries:
    """Exact complex samples represented by integer Nx2 numerators and one denominator."""

    def __init__(self, numerators, denominator):
        if denominator <= 0 or numerators.ndim != 2 or numerators.shape[1] != 2:
            raise AssertionError("invalid rational series")
        self.numerators = numerators
        self.denominator = int(denominator)

    def __len__(self):
        return self.numerators.shape[0]

    def __getitem__(self, item):
        if isinstance(item, slice):
            return RationalSeries(self.numerators[item], self.denominator)
        value = self.numerators[item]
        return complex_pair(Q(int(value[0]), self.denominator), Q(int(value[1]), self.denominator))

    def subtract(self, other):
        if len(self) != len(other):
            raise AssertionError("different rational series extents")
        denominator = math.lcm(self.denominator, other.denominator)
        left_factor = denominator // self.denominator
        right_factor = denominator // other.denominator
        values = np.empty((len(self), 2), dtype=object)
        values[:, 0] = self.numerators[:, 0] * left_factor - other.numerators[:, 0] * right_factor
        values[:, 1] = self.numerators[:, 1] * left_factor - other.numerators[:, 1] * right_factor
        return RationalSeries(values, denominator)


def series_from_pairs(values):
    denominator = 1
    for value in values:
        denominator = math.lcm(denominator, value[0].denominator, value[1].denominator)
    numerators = np.empty((len(values), 2), dtype=object)
    for index, value in enumerate(values):
        numerators[index, 0] = int(value[0] * denominator)
        numerators[index, 1] = int(value[1] * denominator)
    return RationalSeries(numerators, denominator)


def real_series(values, denominator):
    numerators = np.empty((len(values), 2), dtype=object)
    numerators[:, 0] = np.asarray(values, dtype=object)
    numerators[:, 1] = 0
    return RationalSeries(numerators, denominator)


def convolve_signal(source, response, source_denominator):
    """Convolve an integer real source with a small exact complex response."""
    response = series_from_pairs(response)
    source = np.asarray(source, dtype=object)
    values = np.zeros((len(source) + len(response) - 1, 2), dtype=object)
    for offset in range(len(response)):
        values[offset:offset + len(source), 0] += source * response.numerators[offset, 0]
        values[offset:offset + len(source), 1] += source * response.numerators[offset, 1]
    return RationalSeries(values, source_denominator * response.denominator)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve_path(value, report_path):
    path = Path(value)
    if path.is_absolute() or path.exists():
        return path
    return report_path.parent / path


def pcm(path):
    with wave.open(str(path), "rb") as recording:
        if recording.getnchannels() != 1 or recording.getsampwidth() != 2:
            raise AssertionError(f"expected mono PCM16 WAV: {path}")
        rate, frames = recording.getframerate(), recording.getnframes()
        values = np.frombuffer(recording.readframes(frames), dtype="<i2")
    if len(values) != frames:
        raise AssertionError(f"short WAV payload: {path}")
    return rate, values.astype(np.int64)


def verify_occurrence(metadata, report_path):
    path = resolve_path(metadata["path"], report_path)
    if digest(path) != metadata["sha256"]:
        raise AssertionError(f"WAV hash mismatch: {path}")
    if path.stat().st_size != metadata["octets"]:
        raise AssertionError(f"WAV size mismatch: {path}")
    rate, values = pcm(path)
    if rate != metadata["sample_rate"] or len(values) != metadata["frames"]:
        raise AssertionError(f"WAV metadata mismatch: {path}")
    return path, rate, values


def wide_from_pairs(pairs, at):
    lo = pairs[2 * at]
    hi = pairs[2 * at + 1]
    if lo[0] != lo[1] or hi[0] != hi[1]:
        raise AssertionError(f"non-point W at {at}")
    unsigned = (int(hi[0]) & MASK64) << 64 | (int(lo[0]) & MASK64)
    return unsigned - TWO128 if unsigned >> 127 else unsigned


def load_section(metadata, report_path):
    path = resolve_path(metadata["section_path"], report_path)
    data = path.read_bytes()
    if digest(path) != metadata["section_sha256"]:
        raise AssertionError(f"section hash mismatch: {path}")
    if len(data) != metadata["section_octets"] or data[:8] != RESIDENT_SECTION_REST_MAGIC:
        raise AssertionError(f"section envelope mismatch: {path}")
    if len(data) < 40:
        raise AssertionError(f"short section: {path}")
    rows, width, grain, bound, population = struct.unpack_from("<QQIIQ", data, 8)
    if len(data) != 40 + 16 * population or population != rows * width:
        raise AssertionError(f"section shape mismatch: {path}")
    if metadata.get("section_wire"):
        wire = metadata["section_wire"]
        if (rows, width, grain, bound) != (
            wire["rows"], wire["width"], wire["grain"], wire["bound_octaves"]
        ):
            raise AssertionError(f"section wire metadata mismatch: {path}")
    pairs = np.frombuffer(data, dtype="<i8", offset=40, count=2 * population).reshape(population, 2)
    if not np.array_equal(pairs[:, 0], pairs[:, 1]):
        raise AssertionError(f"uncertain serialized W endpoints: {path}")
    return {"path": path, "rows": rows, "width": width, "grain": grain,
            "bound": bound, "population": population, "pairs": pairs}


def decode_ball(metadata, report_path):
    section = load_section(metadata, report_path)
    raw = int(metadata["raw_extent"])
    grain = int(metadata["grain"])
    offset = int(metadata["wide_offset"])
    if section["rows"] != 1 or section["grain"] != 0 or section["bound"] != 64 \
            or section["width"] % 2 or raw <= 0 or offset < 0 or grain < 1 or grain > 120:
        raise AssertionError("invalid enclosure metadata")
    needed = offset + 2 * raw + 1
    if needed > section["width"] // 2:
        raise AssertionError("enclosure offset outside section")
    coordinates = section["pairs"][2 * offset:2 * (offset + 2 * raw):2]
    high_words = section["pairs"][2 * offset + 1:2 * (offset + 2 * raw):2]
    numerators = np.empty((raw, 2), dtype=object)
    for index in range(raw):
        lo_real, lo_imag = int(coordinates[2 * index, 0]), int(coordinates[2 * index + 1, 0])
        hi_real, hi_imag = int(high_words[2 * index, 0]), int(high_words[2 * index + 1, 0])
        numerators[index, 0] = (lo_real & MASK64) + (hi_real << 64)
        numerators[index, 1] = (lo_imag & MASK64) + (hi_imag << 64)
    radius = wide_from_pairs(section["pairs"], offset + 2 * raw)
    if radius < 0:
        raise AssertionError("negative enclosure radius")
    scale = 1 << grain
    return {"section": section, "numerators": numerators, "radius_num": radius,
            "scale": scale,
            "raw_extent": raw, "grain": grain, "wide_offset": offset}


def contains(ball, expected, label):
    if not isinstance(expected, RationalSeries):
        expected = series_from_pairs(expected)
    if len(expected) != ball["raw_extent"]:
        raise AssertionError(f"{label} extent mismatch")
    radius_num = ball["radius_num"]
    scale = ball["scale"]
    radius_squared = radius_num * radius_num * expected.denominator * expected.denominator
    actual = ball["numerators"]
    wanted = expected.numerators
    squared_error = 0
    for index in range(len(expected)):
        real_delta = int(actual[index, 0]) * expected.denominator - int(wanted[index, 0]) * scale
        imag_delta = int(actual[index, 1]) * expected.denominator - int(wanted[index, 1]) * scale
        squared_error += real_delta * real_delta + imag_delta * imag_delta
        if squared_error > radius_squared:
            raise AssertionError(f"{label} exceeds its global Euclidean radius by coordinate {index}")
    return {"coordinates": 2 * len(expected), "radius": str(Q(radius_num, scale)),
            "squared_error": str(Q(squared_error, (scale * expected.denominator) ** 2)), "contains": True}


def exact_values(metadata):
    result = []
    for value in metadata:
        result.append(complex_pair(Q(value["real"]), Q(value["imaginary"])))
    return result


def solve(matrix, rhs):
    matrix = [[Q(value) for value in row] for row in matrix]
    rhs = [Q(value) for value in rhs]
    n = len(rhs)
    if n == 0 or len(matrix) != n or any(len(row) != n for row in matrix):
        raise AssertionError("empty or non-square exact solve")
    for column in range(n):
        pivot = next((row for row in range(column, n) if matrix[row][column]), None)
        if pivot is None:
            raise AssertionError("singular exact temporal Gram")
        if pivot != column:
            matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
            rhs[pivot], rhs[column] = rhs[column], rhs[pivot]
        divisor = matrix[column][column]
        for j in range(column, n):
            matrix[column][j] /= divisor
        rhs[column] /= divisor
        for row in range(n):
            if row == column or not matrix[row][column]:
                continue
            factor = matrix[row][column]
            for j in range(column, n):
                matrix[row][j] -= factor * matrix[column][j]
            rhs[row] -= factor * rhs[column]
    return rhs


def temporal_operands(source, observed, support, taps, divisor):
    p = int(support["predicted"]["start"])
    end = int(support["predicted"]["end"])
    o = int(support["observed"]["start"])
    length = end - p
    n = len(source)
    if end > n + taps - 1 or o + length > len(observed):
        raise AssertionError("support exceeds causal operands")
    dimension = 2 * taps
    gram = [[0 for _ in range(dimension)] for _ in range(dimension)]
    raw = [0 for _ in range(dimension)]
    for k in range(taps):
        raw_real = 0
        raw_begin, raw_end = max(p, k), min(end, k + n)
        for index in range(raw_begin, raw_end):
            raw_real += int(source[index - k]) * int(observed[o + index - p])
        raw[2 * k] = raw_real
        for l in range(taps):
            begin = max(p, k, l)
            stop = min(end, k + n, l + n)
            value = sum(int(source[index - k]) * int(source[index - l])
                        for index in range(begin, stop))
            row, column = 2 * k, 2 * l
            gram[row][column] = value
            gram[row + 1][column + 1] = value
            gram[row][column + 1] = 0
            gram[row + 1][column] = 0
    return gram, raw


def temporal_solve(gram, raw, prior, px, py, cden):
    dimension = len(raw)
    matrix = [[Q(value) for value in row] for row in gram]
    rhs = []
    for row in range(dimension):
        matrix[row][row] += cden
        rhs.append(cden * (prior[row // 2][0] if row % 2 == 0 else prior[row // 2][1])
                   + Q(px, py) * raw[row])
    solution = solve(matrix, rhs)
    return [complex_pair(solution[2 * i], solution[2 * i + 1]) for i in range(dimension // 2)]


def convolve(source, response):
    output = [ZERO for _ in range(len(source) + len(response) - 1)]
    for i, value in enumerate(source):
        if value[0] or value[1]:
            for j, coefficient in enumerate(response):
                output[i + j] = pair_add(output[i + j], pair_mul(value, coefficient))
    return output


def subtract(left, right):
    if len(left) != len(right):
        raise AssertionError("different subtraction extents")
    if isinstance(left, RationalSeries) and isinstance(right, RationalSeries):
        return left.subtract(right)
    return [pair_sub(a, b) for a, b in zip(left, right)]


def outside_ranges(start, end, extent):
    result = []
    if start:
        result.append({"start": 0, "end": start})
    if end < extent:
        result.append({"start": end, "end": extent})
    return result


def check_view(metadata, raw, grain, rate, receiver, lineage, offset=0):
    if (metadata["raw_extent"], metadata["grain"], metadata["receiver"], metadata["lineage"],
            metadata["wide_offset"], metadata["phase_extent"]) != (raw, grain, receiver, lineage, offset, 4) \
            or Q(metadata["origin"]) != 0 or Q(metadata["sample_step"]) != Q(1, rate):
        raise AssertionError("temporal receiver, clock, lineage or enclosure chart changed")


def decode_tail(metadata, report_path, taps):
    section = load_section(metadata, report_path)
    d = 2 * taps
    segment = d + 1
    offset = int(metadata["wide_offset"])
    base = offset - 3 * segment
    if base != 0:
        raise AssertionError("successor offset cannot locate contact report")
    tail = base + 8 * segment
    if tail + d * d + d + 3 != section["width"] // 2:
        raise AssertionError("contact report tail outside section")
    gram = [[wide_from_pairs(section["pairs"], tail + row * d + column)
             for column in range(d)] for row in range(d)]
    raw = [wide_from_pairs(section["pairs"], tail + d * d + i) for i in range(d)]
    scalars = [wide_from_pairs(section["pairs"], tail + d * d + d + i) for i in range(3)]
    if any(value <= 0 for value in scalars):
        raise AssertionError("non-positive retained temporal denominator")
    px, py, cden = scalars
    blocks = [[wide_from_pairs(section["pairs"], i * segment + j)
               for j in range(segment)] for i in range(8)]
    prior, v, u, h, returned, delta, residual_u, residual_v = blocks
    scale = 1 << int(metadata["grain"])
    for i in range(d):
        au = sum((gram[i][j] + (cden if i == j else 0)) * u[j] for j in range(d))
        av = sum((gram[i][j] + (cden if i == j else 0)) * v[j] for j in range(d))
        if residual_u[i] != py * au - px * raw[i] * scale \
                or residual_v[i] != av - cden * prior[i]:
            raise AssertionError("contact solve residual changed")
        if h[i] != u[i] + v[i] or returned[i] != prior[i] - v[i] or delta[i] != h[i] - prior[i]:
            raise AssertionError("contact normal-current decomposition changed")
    if residual_u[-1] != py * cden or residual_v[-1] != cden or prior[-1] < 0:
        raise AssertionError("contact residual denominator changed")
    ceiling = lambda n, den: (n + den - 1) // den
    ru = ceiling(sum(abs(v) for v in residual_u[:-1]), py * cden)
    rv = prior[-1] + ceiling(sum(abs(v) for v in residual_v[:-1]), cden)
    if [b[-1] for b in blocks[1:6]] != [rv, ru, ru + rv, prior[-1] + rv, ru + rv + prior[-1]]:
        raise AssertionError("contact certified radius changed")
    return {"gram": gram, "raw": raw, "px": scalars[0], "py": scalars[1], "cden": scalars[2]}


def verify_acquisition(report, report_path, acquisition_path):
    if acquisition_path is None:
        raise AssertionError("source qualification requires the acquisition receipt")
    acquisition = json.loads(Path(acquisition_path).read_text())
    if acquisition.get("schema") != "soundcam-selective-acquisition.v1":
        raise AssertionError("unknown acquisition schema")
    root = Path(acquisition_path).parent
    for pair_report in report["pairs"]:
        matches = []
        for pair in acquisition["pairs"]:
            source = (root / pair["loopback"]["path"]).resolve()
            observed = (root / pair["microphone_recording"]["path"]).resolve()
            if source == resolve_path(pair_report["excitation"]["path"], report_path).resolve() \
                    and observed == resolve_path(pair_report["observation"]["path"], report_path).resolve():
                matches.append(pair)
        if len(matches) != 1:
            raise AssertionError("report pair missing unique acquisition provenance")
        match = matches[0]
        if match["origin_frame"] != 0:
            raise AssertionError("source pair is not on the declared zero-origin clock")
        for role, key in (("excitation", "loopback"), ("observation", "microphone_recording")):
            metadata = pair_report[role]
            if metadata["sha256"] != match[key]["wav_sha256"]:
                raise AssertionError("acquisition WAV hash mismatch")
            path, rate, values = verify_occurrence(metadata, report_path)
            if rate != match["sample_rate_hz"] or len(values) != match[key]["frames"]:
                raise AssertionError("acquisition sample metadata mismatch")
            raw_key = "music_directlines_npy" if role == "excitation" else "music_audio_npy"
            raw_path = (root / acquisition["raw_outputs"][raw_key]).resolve()
            if digest(raw_path) != match[key]["source_array_sha256"]:
                raise AssertionError("acquisition raw-array hash mismatch")
            raw = np.load(raw_path, mmap_mode="r", allow_pickle=False)
            if raw.dtype.str != "<i2":
                raise AssertionError("acquisition raw array is not little-endian int16")
            selected = raw[match["row"]] if role == "excitation" else raw[match["row"], match["microphone"]]
            if not np.array_equal(selected, values):
                raise AssertionError(f"acquisition raw array differs from {path}")
    return True


def verify_report(report_path, acquisition_path=None):
    report_path = Path(report_path)
    report = json.loads(report_path.read_text())
    if report.get("schema") != "holonics.recorded-acoustic-contact.v1" or report.get("status") != "returned":
        raise AssertionError("unexpected contact report schema/status")
    if not report.get("sound_model") is False or not report.get("conversation_model") is False:
        raise AssertionError("report scope flags are not explicit")
    acquisition_verified = verify_acquisition(report, report_path, acquisition_path)
    pairs = report.get("pairs")
    if not pairs:
        raise AssertionError("contact report has no pairs")
    taps = int(report["response_control"]["taps"])
    grain = int(report["response_control"]["grain"])
    divisor = int(report["pcm_divisor"])
    if taps <= 0 or not 1 <= grain <= 120 or divisor != 32768 or report["phase_extent"] != 4:
        raise AssertionError("invalid contact controls")
    if report["response_control"]["initial"] != "h[0]=1, all remaining taps=0" \
            or report["contacts"] != len(pairs):
        raise AssertionError("initial current or contact count changed")
    initial = [complex_pair(1, 0)] + [ZERO for _ in range(taps - 1)]
    prior_exact = initial
    prior_successor_cut = None
    checked = []
    rates = set()
    for pair_index, pair in enumerate(pairs):
        if pair["pair"] != pair_index:
            raise AssertionError("recording order changed")
        source_path, source_rate, source = verify_occurrence(pair["excitation"], report_path)
        observed_path, observed_rate, observed = verify_occurrence(pair["observation"], report_path)
        if source_rate != observed_rate:
            raise AssertionError("source/observation sample rates differ")
        rates.add(source_rate)
        chronology = pair["chronology"]
        expected_cut = pair_index if prior_successor_cut is None else prior_successor_cut
        if chronology["pre_contact_cut"] != expected_cut or chronology["current_cut"] != expected_cut \
                or chronology["successor_cut"] != expected_cut + 1:
            raise AssertionError("contact chronology does not continue the previous successor")
        support = pair["support"]
        predicted_range = support["predicted"]
        observed_range = support["observed"]
        if predicted_range["start"] < 0 or predicted_range["end"] <= predicted_range["start"] \
                or observed_range["start"] < 0 or observed_range["end"] <= observed_range["start"] \
                or predicted_range["end"] - predicted_range["start"] != observed_range["end"] - observed_range["start"]:
            raise AssertionError(f"invalid comparison support at pair {pair_index}")
        prediction_extent = len(source) + taps - 1
        extent = min(prediction_extent, len(observed))
        if predicted_range != {"start": 0, "end": extent} or observed_range != predicted_range \
                or native_fraction(support["begin"]) != 0 \
                or native_fraction(support["end"]) != Q(extent, source_rate):
            raise AssertionError("comparison no longer uses full common zero-origin support")
        if support.get("unobserved_prediction") != outside_ranges(
                predicted_range["start"], predicted_range["end"], prediction_extent):
            raise AssertionError(f"prediction exclusion metadata changed at pair {pair_index}")
        if support.get("unpredicted_observation") != outside_ranges(
                observed_range["start"], observed_range["end"], len(observed)):
            raise AssertionError(f"observation exclusion metadata changed at pair {pair_index}")
        gram_expected, raw_expected = temporal_operands(source, observed, support, taps, divisor)
        gcd = math.gcd(divisor, divisor)
        px, py, cden = divisor // gcd, divisor // gcd, divisor * divisor
        tail = decode_tail(pair["contact_report"], report_path, taps)
        if tail["gram"] != gram_expected or tail["raw"] != raw_expected \
                or (tail["px"], tail["py"], tail["cden"]) != (px, py, cden):
            raise AssertionError(f"retained exact temporal tail mismatch at pair {pair_index}")
        expected = temporal_solve(gram_expected, raw_expected, prior_exact, px, py, cden)
        reading = pair["condition_reading"]
        if exact_values(reading["response"]) != expected:
            raise AssertionError(f"cold exact response mismatch at pair {pair_index}")
        if reading.get("prior") is not None and exact_values(reading["prior"]) != prior_exact:
            raise AssertionError(f"cold prior mismatch at pair {pair_index}")
        changed = expected != prior_exact
        if reading.get("response_changed") != changed:
            raise AssertionError(f"response_changed is not derived from exact responses at pair {pair_index}")
        predicted = convolve_signal(source, prior_exact, divisor)
        p = int(support["predicted"]["start"])
        o = int(support["observed"]["start"])
        length = int(support["predicted"]["end"]) - p
        observed_support = real_series(observed[o:o + length], divisor)
        difference = subtract(observed_support, predicted[p:p + length])
        # Solve the two exact normal components separately for the paired reports.
        u = temporal_solve(gram_expected, raw_expected, [ZERO] * taps, px, py, cden)
        v = temporal_solve(gram_expected, [0] * (2 * taps), prior_exact, 0, 1, cden)
        # temporal_solve with px=0 gives the prior term; its raw is zero by construction.
        returned_h = subtract(prior_exact, v)
        h_difference = subtract(expected, prior_exact)
        incoming_e = subtract(observed_support,
                              convolve_signal(source, u, divisor)[p:p + length])
        returned_e = convolve_signal(source, v, divisor)
        unexplained = subtract(observed_support,
                               convolve_signal(source, expected, divisor)[p:p + length])
        pair_checked = {
            "pair": pair_index,
            "source": str(source_path),
            "observation": str(observed_path),
            "sample_rate": source_rate,
            "frames": len(source),
            "tail": {"gram_entries": (2 * taps) ** 2, "raw_entries": 2 * taps,
                     "px": px, "py": py, "cden": cden},
            "excluded_tail_metadata_verified": True,
            "exact_response": [str(value[0]) + "+" + str(value[1]) + "i" for value in expected],
            "response_changed": changed,
        }
        for name, values in (("prediction", predicted), ("difference", difference),
                             ("unexplained", unexplained), ("incoming_normal_e", incoming_e)):
            meta = pair[name]
            lineage = 20 + pair_index * 10 + (0 if name == "prediction" else 1 if name == "difference" else 2)
            check_view(meta, len(values), grain, source_rate, 9, lineage)
            ball = decode_ball(meta, report_path)
            pair_checked[name] = contains(ball, values, f"pair {pair_index} {name}")
        returned_meta = pair["returned_normal_e"]
        check_view(returned_meta, prediction_extent, grain, source_rate, 9, 22 + pair_index * 10)
        returned_ball = decode_ball(returned_meta, report_path)
        support_meta = returned_meta.get("normal_support")
        if support_meta != support["predicted"]:
            raise AssertionError(f"returned normal support changed at pair {pair_index}")
        pair_checked["returned_normal_e"] = contains(
            returned_ball, returned_e, f"pair {pair_index} returned_normal_e")
        offsets = pair["normal_leg_offsets"]
        contact_meta = pair["contact_report"]
        check_view(contact_meta, taps, grain, source_rate, 8, 22 + pair_index * 10, 3 * (2 * taps + 1))
        if offsets["section_path"] != contact_meta["section_path"] \
                or offsets["section_sha256"] != contact_meta["section_sha256"]:
            raise AssertionError("normal legs refer to a different contact carrier")
        block_ids = {"incoming_h": 2, "returned_h": 4, "difference_h": 5, "successor": 3}
        for name, values in (("incoming_h", u), ("returned_h", returned_h),
                             ("difference_h", h_difference), ("successor", expected)):
            if offsets[name] != {"grain":grain,"wide_offset":block_ids[name] * (2 * taps + 1)}:
                raise AssertionError("normal-leg report offset changed")
            ball = decode_ball({**contact_meta, **offsets[name]}, report_path)
            pair_checked[name] = contains(ball, values, f"pair {pair_index} {name}")
        for name, values, block in (("prior", prior_exact, 0), ("v", v, 1)):
            ball = decode_ball({**contact_meta,"wide_offset":block * (2 * taps + 1)}, report_path)
            pair_checked[name] = contains(ball, values, f"pair {pair_index} {name}")
        successor_ball = decode_ball(pair["contact_report"], report_path)
        pair_checked["successor_report"] = contains(successor_ball, expected, f"pair {pair_index} successor")
        for suffix, deeds in (("predict_before_observation",1),("compare_observation",1),("native_temporal_contact",6)):
            name = f"pair_{pair_index}_{suffix}"
            stage = report["stages"][name]
            if stage["deeds"] != deeds or stage["section_readouts"] != 0 \
                    or stage["numerical_egress_octets"] != 0 or stage["ingress_octets"] != 0:
                raise AssertionError(f"hot stage is not resident-only: {name}")
        if pair.get("hot_zero_numerical_reads") is not True:
            raise AssertionError(f"report hot-read flag is false at pair {pair_index}")
        checked.append(pair_checked)
        prior_exact = expected
        prior_successor_cut = chronology["successor_cut"]
    if len(rates) != 1:
        raise AssertionError("continuing response changed its sample clock")
    native_changed = any(item["response_changed"] for item in checked)
    if report.get("native_response_changed") != native_changed:
        raise AssertionError("native_response_changed is not independently derived")
    return {"verified": True, "report": str(report_path), "pairs": checked,
            "sample_rates": sorted(rates), "acquisition_provenance": acquisition_verified,
            "native_hot_numeric_reads": False,
            "scope": "cold exact source-qualified temporal contact; no native execution"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", type=Path, nargs="+")
    parser.add_argument("--acquisition", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    paths = list(args.paths)
    acquisition = args.acquisition
    if acquisition is None and len(paths) >= 2:
        try:
            first = json.loads(paths[0].read_text())
        except (OSError, json.JSONDecodeError):
            first = {}
        if first.get("schema") == "soundcam-selective-acquisition.v1":
            acquisition, paths = paths[0], paths[1:]
    if not paths:
        parser.error("at least one contact report is required")
    results = [verify_report(path, acquisition) for path in paths]
    rendered = json.dumps({"verified": True, "comparisons": results}, indent=2) + "\n"
    if args.output:
        with args.output.open("x") as output:
            output.write(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
