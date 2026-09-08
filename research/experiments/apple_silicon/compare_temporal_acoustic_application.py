#!/usr/bin/env python3
"""Cold source-qualified check of the public temporal acoustic application boundary."""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import math
from pathlib import Path
import struct
import wave

from compare_recorded_acoustic_contact import (
    RationalSeries,
    convolve_signal,
    decode_ball,
    load_section,
    native_fraction,
    resolve_path,
)

SECTION_MAGIC = b"HRSRST\0\x01"
CHECKPOINT_MAGIC = b"HNA-TEMPORAL-ACOUSTIC\x01"
CHECKPOINT_END = b"HNA-TEMPORAL-ACOUSTIC-END\x01"
REST_MAGIC = b"HNA-TEMPORAL-CONDITION-REST\x01"
REST_END = b"HNA-TEMPORAL-CONDITION-END\x01"
PCM_DIVISOR = 32768
MASK64 = (1 << 64) - 1
TWO128 = 1 << 128


def fail(message):
    raise ValueError(message)


def rational(value):
    if isinstance(value, (int, str)):
        return Q(value)
    return native_fraction(value)


def blob(data, at, end):
    if at + 8 > end:
        fail("truncated blob length")
    length = struct.unpack_from("<Q", data, at)[0]
    at += 8
    if length > end - at:
        fail("blob exceeds containing extent")
    return data[at:at + length], at + length


def json_blob(data, at, end):
    raw, at = blob(data, at, end)
    try:
        return json.loads(raw), at
    except json.JSONDecodeError as error:
        fail(f"malformed JSON blob: {error}")


def parse_section(raw):
    if not raw.startswith(SECTION_MAGIC) or len(raw) < 40:
        fail("resident section carrier")
    rows, width, grain, bound, population = struct.unpack_from("<QQIIQ", raw, 8)
    if rows == 0 or width == 0 or rows * width != population:
        fail("resident section shape")
    if len(raw) != 40 + 16 * population:
        fail("resident section extent")
    if grain != 0 or bound != 64:
        fail("temporal section aperture")
    return {"raw": raw, "rows": rows, "width": width, "grain": grain,
            "bound": bound, "population": population}


def section_words(section):
    values = []
    for index in range(section["population"]):
        left, right = struct.unpack_from("<qq", section["raw"], 40 + 16 * index)
        if left != right:
            fail("resident section contains an interval instead of a point")
        values.append(left)
    return values


def section_wide_values(section):
    words = section_words(section)
    if len(words) % 2:
        fail("wide section has an odd word population")
    values = []
    for index in range(0, len(words), 2):
        unsigned = (words[index] & MASK64) | ((words[index + 1] & MASK64) << 64)
        values.append(unsigned - TWO128 if unsigned >> 127 else unsigned)
    return values


def verify_reference_section(metadata, reference_path):
    section = load_section(metadata, reference_path)
    if hashlib.sha256(section["path"].read_bytes()).hexdigest() != metadata["section_sha256"] \
            or section["path"].stat().st_size != metadata["section_octets"]:
        fail("validated reference section hash/extent")
    return section


def parse_rest(raw):
    if not raw.startswith(REST_MAGIC):
        fail("temporal rest magic")
    end = len(raw)
    header, at = json_blob(raw, len(REST_MAGIC), end)
    initial_raw, at = blob(raw, at, end)
    initial_ball_raw, at = blob(raw, at, end)
    initial = parse_section(initial_raw)
    initial_ball = parse_section(initial_ball_raw)
    contacts = header.get("contacts")
    if not isinstance(contacts, list):
        fail("temporal rest contacts")
    reports = []
    for _ in contacts:
        section_raw, at = blob(raw, at, end)
        reports.append(parse_section(section_raw))
    if raw[at:] != REST_END:
        fail("temporal rest trailing bytes")
    return {"raw": raw, "header": header, "initial": initial,
            "initial_ball": initial_ball, "reports": reports}


def parse_checkpoint(path):
    path = Path(path)
    data = path.read_bytes()
    minimum = len(CHECKPOINT_MAGIC) + 8 + 8 + 32 + len(CHECKPOINT_END)
    if len(data) < minimum:
        fail("checkpoint minimum extent")
    footer = len(data) - len(CHECKPOINT_END) - 32
    if data[footer + 32:] != CHECKPOINT_END:
        fail("checkpoint footer")
    if hashlib.sha256(data[:footer]).digest() != data[footer:footer + 32]:
        fail("checkpoint checksum")
    if not data.startswith(CHECKPOINT_MAGIC):
        fail("checkpoint kind/version")
    header, at = json_blob(data, len(CHECKPOINT_MAGIC), footer)
    if at + 8 > footer:
        fail("checkpoint native extent")
    native_extent = struct.unpack_from("<Q", data, at)[0]
    at += 8
    if at + native_extent != footer:
        fail("checkpoint native rest extent")
    native_raw = data[at:footer]
    return {"path": path, "header": header, "native": parse_rest(native_raw)}


def verify_checkpoint_chart(checkpoint, reference_pairs, reference_taps):
    chart = checkpoint["header"].get("chart", {})
    sample_rate = reference_pairs[0]["excitation"]["sample_rate"]
    if chart.get("sample_rate") != sample_rate or chart.get("pcm_divisor") != PCM_DIVISOR \
            or chart.get("source_receiver") != 1 or chart.get("output_receiver") != 9:
        fail("checkpoint application chart")
    response_header = checkpoint["native"]["header"]
    response_chart = response_header.get("chart", {})
    if response_chart.get("receiver") != 8 \
            or rational(response_chart.get("origin")) != 0 \
            or response_chart.get("raw_extent") != reference_taps \
            or response_chart.get("phase_extent") != 4 \
            or response_chart.get("sample_step") is None \
            or rational(response_chart["sample_step"]) != Q(1, sample_rate):
        fail("checkpoint response chart")
    if response_header.get("metric") != "UnitAdmittanceRealification":
        fail("checkpoint condition-contact metric")
    if response_header.get("grain") != int(reference_pairs[0]["contact_report"]["grain"]):
        fail("checkpoint response grain")
    initial = checkpoint["native"]["initial"]
    initial_ball = checkpoint["native"]["initial_ball"]
    if initial["rows"] != 1 or initial["width"] != 2 * reference_taps + 1:
        fail("initial response section shape")
    initial_values = section_words(initial)
    expected_initial = [0] * (2 * reference_taps + 1)
    expected_initial[0] = 1
    expected_initial[-1] = 1
    if initial_values != expected_initial:
        fail("initial response is not the explicit unit impulse")
    if initial_ball["rows"] != 1 or initial_ball["width"] != 2 * (2 * reference_taps + 1):
        fail("initial response ball shape")
    ball_words = section_wide_values(initial_ball)
    grain = int(response_header["grain"])
    expected_ball = [0] * (2 * reference_taps + 1)
    expected_ball[0] = 1 << grain
    if ball_words[:2 * reference_taps + 1] != expected_ball or ball_words[-1] != 0:
        fail("initial response ball differs from explicit impulse")
    return sample_rate


def verify_checkpoint_reports(checkpoint, history, reference_pairs, reference_path, reference_taps):
    if checkpoint["header"].get("history") != history:
        fail("checkpoint history differs from application history")
    reports = checkpoint["native"]["reports"]
    if len(reports) != len(history):
        fail("checkpoint contact report population")
    expected_at = 3 * (2 * reference_taps + 1)
    for receipt in history:
        cut = receipt["producing_cut"]
        if cut not in reference_pairs:
            fail("checkpoint contact cut outside reference")
        contacts = checkpoint["native"]["header"].get("contacts", [])
        if cut >= len(contacts):
            fail("checkpoint contact metadata population")
        contact_header = contacts[cut]
        if contact_header.get("cut") != cut + 1 \
                or contact_header.get("at") != expected_at \
                or contact_header.get("lineage") != receipt["contact_lineage"]:
            fail("checkpoint contact chronology metadata")
        reference_metadata = reference_pairs[cut]["contact_report"]
        reference_section = verify_reference_section(reference_metadata, reference_path)
        if reference_metadata.get("wide_offset") != expected_at:
            fail("reference contact report offset")
        if reports[cut]["raw"] != reference_section["path"].read_bytes():
            fail("checkpoint contact report section differs from validated reference")


def read_wav(path, channels):
    path = Path(path)
    raw = path.read_bytes()
    with wave.open(str(path), "rb") as recording:
        if recording.getnchannels() != channels or recording.getsampwidth() != 2:
            fail(f"WAV is not PCM16 with {channels} channels: {path}")
        rate = recording.getframerate()
        frames = recording.getnframes()
        payload = recording.readframes(frames)
    if len(payload) != frames * channels * 2:
        fail(f"short WAV payload: {path}")
    values = struct.unpack(f"<{frames * channels}h", payload)
    return path, raw, rate, frames, values


def verify_recording(metadata, report_path, reference_metadata):
    path = resolve_path(metadata["locator"], report_path)
    _, raw, rate, frames, _ = read_wav(path, 1)
    if hashlib.sha256(raw).hexdigest() != metadata["sha256"] or len(raw) != metadata["octets"]:
        fail(f"application recording hash/extent: {path}")
    if rate != metadata["sample_rate"] or frames != metadata["frames"]:
        fail(f"application recording clock/frames: {path}")
    reference_path = resolve_path(reference_metadata["path"], Path(reference_metadata.get("_report", report_path)))
    if path.resolve() != reference_path.resolve():
        fail("application recording differs from validated reference source")
    for key in ("sha256", "octets", "sample_rate", "frames"):
        if metadata[key] != reference_metadata[key]:
            fail(f"recording provenance differs: {key}")
    return path, rate, frames


def compare_recording_pair(receipt, reference_pair, app_path, reference_path):
    for role, reference_role in (("source", "excitation"), ("observed", "observation")):
        metadata = receipt[role]
        reference = dict(reference_pair[reference_role])
        reference["_report"] = reference_path
        path, rate, frames = verify_recording(metadata, app_path, reference)
        if rational(metadata.get("origin")) != 0:
            fail(f"nonzero application {role} origin")
        if reference.get("sample_rate") != rate or reference.get("frames") != frames:
            fail(f"reference {role} metadata changed")
        if metadata.get("occurrence") == "":
            fail(f"empty application {role} occurrence")
    return True


def reference_pair_map(reference):
    pairs = reference.get("pairs")
    if not isinstance(pairs, list) or not pairs:
        fail("reference contact pairs")
    result = {}
    for index, pair in enumerate(pairs):
        if pair.get("pair") != index or pair.get("chronology", {}).get("pre_contact_cut") != index:
            fail("reference chronology is not the validated sequential record")
        result[index] = pair
    return result


def projection_rat(value):
    return rational(value)


def toward_zero(value):
    return value.numerator // value.denominator if value >= 0 else -((-value.numerator) // value.denominator)


def projection_series(projection):
    frames = projection.get("frames")
    if not isinstance(frames, list) or not frames:
        fail("projection frames")
    values = []
    for frame in frames:
        representative = frame["representative"]
        values.append((projection_rat(representative["real"]),
                       projection_rat(representative["imaginary"])))
    denominator = 1
    for value in values:
        denominator = math.lcm(denominator, value[0].denominator, value[1].denominator)
    import numpy as np
    numerators = np.empty((len(values), 2), dtype=object)
    for index, value in enumerate(values):
        numerators[index, 0] = int(value[0] * denominator)
        numerators[index, 1] = int(value[1] * denominator)
    return RationalSeries(numerators, denominator)


def verify_projection(sound, app_report_path, expected_ball=None, expected_values=None,
                      expected_receiver=9, expected_lineage=None):
    projection_path = resolve_path(sound["projection"], app_report_path)
    projection = json.loads(projection_path.read_text())
    if projection.get("schema") != "soma-life.native-acoustic-enclosed-temporal-pcm16.v1":
        fail("enclosed temporal projection schema")
    wav_path = resolve_path(sound["wav"], app_report_path)
    _, wav_raw, wav_rate, wav_frames, wav_values = read_wav(wav_path, 2)
    if projection.get("sample_rate") != wav_rate or projection.get("sample_rate") != sound["sample_rate"]:
        fail("projection/WAV sample clock")
    if projection.get("frames") is None or len(projection["frames"]) != wav_frames:
        fail("projection/WAV frame extent")
    if projection.get("sample_step") is None or rational(projection["sample_step"]) != Q(1, wav_rate):
        fail("projection sample step")
    if projection.get("receiver") != expected_receiver \
            or rational(projection.get("origin")) != 0:
        fail("projection receiver/origin")
    if expected_lineage is not None and projection.get("lineage") != expected_lineage:
        fail("projection lineage")
    gain = projection_rat(projection["gain"])
    radius = projection_rat(projection["radius"])
    if gain <= 0 or radius < 0 or rational(sound["gain"]) != gain:
        fail("projection gain metadata")
    if not sound.get("wav_is_numerical_representative") or sound.get("channels") != ["real", "imaginary"]:
        fail("projection sound metadata")
    series = projection_series(projection)
    if expected_ball is not None:
        if len(series) != expected_ball["raw_extent"]:
            fail("projection/reference extent")
        scale = expected_ball["scale"]
        for index in range(len(series)):
            if (int(series.numerators[index, 0]) * scale !=
                    int(expected_ball["numerators"][index, 0]) * series.denominator):
                fail("projection representative real differs from reference ball")
            if (int(series.numerators[index, 1]) * scale !=
                    int(expected_ball["numerators"][index, 1]) * series.denominator):
                fail("projection representative imaginary differs from reference ball")
        if radius != Q(expected_ball["radius_num"], scale):
            fail("projection global radius differs from reference ball")
    if expected_values is not None:
        check_global_ball(series, expected_values, radius)
    clipped = 0
    for index, frame in enumerate(projection["frames"]):
        representative = series[index]
        pcm_values = frame.get("pcm")
        remainder = frame.get("remainder")
        flags = frame.get("clipped")
        if not isinstance(pcm_values, list) or len(pcm_values) != 2 or not isinstance(flags, list) or len(flags) != 2:
            fail("projection frame quotient")
        for component, value in enumerate(representative):
            scaled = value * gain
            unbounded = toward_zero(scaled)
            quantized = max(-32768, min(32767, unbounded))
            if pcm_values[component] != quantized:
                fail("projection PCM quotient")
            was_clipped = unbounded != quantized
            if flags[component] is not was_clipped:
                fail("projection clipping flag")
            if projection_rat(remainder["real" if component == 0 else "imaginary"]) != scaled - Q(quantized):
                fail("projection exact quotient remainder")
            if wav_values[2 * index + component] != quantized:
                fail("WAV differs from projection PCM")
            clipped += int(was_clipped)
    if clipped != projection.get("clipped_sample_population") \
            or clipped != sound.get("clipped_coordinates"):
        fail("projection clipping population")
    if sound.get("frames") != len(series) or sound.get("radius_native_units") != str(radius):
        fail("sound projection receipt")
    return {"projection": str(projection_path), "wav": str(wav_path),
            "frames": len(series), "sample_rate": wav_rate,
            "projection_sha256": hashlib.sha256(projection_path.read_bytes()).hexdigest(),
            "wav_sha256": hashlib.sha256(wav_raw).hexdigest(), "clipped": clipped}


def check_global_ball(center, expected, radius):
    if len(center) != len(expected):
        fail("global ball extent")
    denominator = math.lcm(center.denominator, expected.denominator)
    left = denominator // center.denominator
    right = denominator // expected.denominator
    squared = 0
    for index in range(len(center)):
        real = int(center.numerators[index, 0]) * left - int(expected.numerators[index, 0]) * right
        imaginary = int(center.numerators[index, 1]) * left - int(expected.numerators[index, 1]) * right
        squared += real * real + imaginary * imaginary
    if squared > radius * radius * denominator * denominator:
        fail("exact expected current lies outside projection global ball")


def app_contacts(report, reference_pairs, reference_path, reference_taps):
    if report.get("schema") != "holonics.temporal-acoustic-application.v1" \
            or report.get("status") != "returned":
        fail("application report schema/status")
    history = report.get("history")
    results = report.get("results")
    if not isinstance(history, list) or not isinstance(results, list) or len(history) != report.get("contacts"):
        fail("application chronology")
    cuts = [receipt.get("producing_cut") for receipt in history]
    if cuts != list(range(len(cuts))):
        fail("application history cuts are not contiguous")
    mount = report.get("mount", {})
    start_cut = int(mount.get("cut", 0)) if mount.get("kind") == "remount" else 0
    if mount.get("kind") == "explicit_unit_impulse":
        if mount.get("taps") != reference_taps or mount.get("grain") != int(
                reference_pairs[0]["contact_report"]["grain"]):
            fail("application unit-response mount scope")
    elif mount.get("kind") != "remount":
        fail("application mount kind")
    result_cuts = [result.get("contact", {}).get("producing_cut") for result in results]
    if result_cuts != list(range(start_cut, len(history))):
        fail("application results do not cover each newly received contact exactly once")
    if mount.get("kind") not in ("remount", "explicit_unit_impulse") or not 0 <= start_cut <= len(history):
        fail("application mount/cut")
    if mount.get("kind") == "remount":
        if mount.get("cut") != start_cut or mount.get("deeds") != 0 \
                or mount.get("section_readouts") != 0:
            fail("remount performed native work or has an invalid cut")
    for receipt in history:
        cut = receipt.get("producing_cut")
        if cut not in reference_pairs or receipt.get("successor_cut") != cut + 1:
            fail("application contact cut")
        if receipt.get("support") != reference_pairs[cut].get("support"):
            fail("application comparison support differs from reference")
        base = 16 + 8 * cut
        if receipt.get("prediction_lineage") != base + 2 or receipt.get("difference_lineage") != base + 3 or receipt.get("contact_lineage") != base + 4:
            fail("application contact lineage")
        compare_recording_pair(receipt, reference_pairs[cut], report["_path"], reference_path)
    for result in results:
        receipt = result.get("contact")
        if receipt not in history:
            fail("application result is absent from history")
        cut = receipt["producing_cut"]
        verify_projection(result["sound"], report["_path"],
                          decode_ball(reference_pairs[cut]["prediction"], reference_path),
                          expected_lineage=receipt["prediction_lineage"])
        for name, deeds in (("prediction_work", 1), ("difference_work", 1), ("contact_work", 6)):
            work = result.get(name, {})
            if work.get("deeds") != deeds or work.get("section_readouts") != 0 \
                    or work.get("numerical_egress_octets") != 0 or work.get("ingress_octets") != 0:
                fail(f"application resident work accounting: {name}")
    checkpoint_path = resolve_path(report["checkpoint"], report["_path"])
    checkpoint = parse_checkpoint(checkpoint_path)
    header = checkpoint["header"]
    sample_rate = verify_checkpoint_chart(checkpoint, reference_pairs, reference_taps)
    verify_checkpoint_reports(checkpoint, history, reference_pairs, reference_path, reference_taps)
    return {"report": str(report["_path"]), "contacts": len(history),
            "checkpoint": str(checkpoint_path), "checkpoint_reports_byte_equal": True,
            "projections_checked": len(results)}


def verify_prediction(path, reference_pairs, reference_path, divisor):
    report_path = Path(path)
    report = json.loads(report_path.read_text())
    if report.get("schema") != "holonics.temporal-acoustic-prediction.v1" \
            or report.get("status") != "returned" or report.get("condition_updated") is not False:
        fail("prediction report schema/status")
    checkpoint_path = resolve_path(report["checkpoint"], report_path)
    checkpoint = parse_checkpoint(checkpoint_path)
    history = checkpoint["header"].get("history")
    reference_taps = len(reference_pairs[max(reference_pairs)]["condition_reading"]["response"])
    if not isinstance(history, list) or len(history) != len(reference_pairs):
        fail("prediction checkpoint history")
    verify_checkpoint_chart(checkpoint, reference_pairs, reference_taps)
    verify_checkpoint_reports(checkpoint, history, reference_pairs, reference_path, reference_taps)
    for receipt in history:
        compare_recording_pair(receipt, reference_pairs[receipt["producing_cut"]],
                               report_path, reference_path)
    remount = report.get("remount", {})
    work = report.get("prediction_work", {})
    if remount.get("deeds") != 0 or remount.get("section_readouts") != 0:
        fail("prediction remount replay/readout")
    if work.get("deeds") != 1 or any(work.get(key) != 0 for key in ("section_readouts", "numerical_egress_octets", "ingress_octets")):
        fail("prediction native accounting")
    if [r.get("producing_cut") for r in history] != list(range(len(history))):
        fail("prediction saved chronology")
    source_path = resolve_path(report["source"], report_path)
    _, raw, rate, frames, samples = read_wav(source_path, 1)
    if hashlib.sha256(raw).hexdigest() != report["source_sha256"] \
            or len(raw) != report["source_octets"] or rate != report["sound"]["sample_rate"] \
            or rate != reference_pairs[max(reference_pairs)]["excitation"]["sample_rate"]:
        fail("prediction source provenance")
    latest = reference_pairs[max(reference_pairs)]
    response = [(rational(value["real"]), rational(value["imaginary"]))
                for value in latest["condition_reading"]["response"]]
    expected = convolve_signal(samples, response, divisor)
    result = verify_projection(report["sound"], report_path, expected_values=expected,
                               expected_lineage=(1 << 64) - 1)
    if report.get("response_cut") != latest["chronology"]["successor_cut"]:
        fail("prediction response chronology")
    return {"report": str(report_path), "source": str(source_path),
            "frames": frames, "sample_rate": rate, "checkpoint": str(checkpoint_path),
            "exact_response_projection": result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("returns", type=Path, nargs="+")
    parser.add_argument("--prediction", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        fail(f"output already exists: {args.output}")
    reference_path = args.reference
    reference = json.loads(reference_path.read_text())
    if reference.get("schema") != "holonics.recorded-acoustic-contact.v1" \
            or reference.get("status") != "returned":
        fail("reference contact report is not the validated bounded record")
    pairs = reference_pair_map(reference)
    reference_taps = int(reference.get("response_control", {}).get("taps", 0))
    if reference_taps != 4 or reference.get("phase_extent") != 4:
        fail("observer scope requires the four-tap, phase-extent-four reference baseline")
    reference_rates = {pair["excitation"]["sample_rate"] for pair in pairs.values()} \
        | {pair["observation"]["sample_rate"] for pair in pairs.values()}
    if len(reference_rates) != 1:
        fail("reference pairs do not share their original sample clock")
    divisor = int(reference["pcm_divisor"])
    if divisor != PCM_DIVISOR:
        fail("observer scope requires the PCM16 divisor baseline")
    comparisons = []
    last_cut = -1
    for path in args.returns:
        report = json.loads(path.read_text())
        report["_path"] = path
        comparison = app_contacts(report, pairs, reference_path, reference_taps)
        cuts = [item["producing_cut"] for item in report["history"]]
        if cuts and cuts[-1] <= last_cut:
            fail("application returns do not continue chronologically")
        if cuts:
            last_cut = cuts[-1]
        comparisons.append(comparison)
    prediction = verify_prediction(args.prediction, pairs, reference_path, divisor) if args.prediction else None
    reference_sha256 = hashlib.sha256(reference_path.read_bytes()).hexdigest()
    result = {"verified": True, "scope": "cold application/checkpoint/PCM boundary; no sound-model claim",
              "reference": str(reference_path),
              "reference_evidence": {
                  "sha256": reference_sha256,
                  "assumed_prevalidated_bounded_evidence": True,
                  "assumptions": {
                      "response_taps": 4, "phase_extent": 4,
                      "pcm_divisor": PCM_DIVISOR,
                      "original_sample_rate": next(iter(reference_rates)),
                      "alignment": "caller-declared zero-origin original recording clock",
                  },
              },
              "comparisons": comparisons,
              "prediction": prediction, "native_execution": False}
    with args.output.open("x") as output:
        json.dump(result, output, indent=2)
        output.write("\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
