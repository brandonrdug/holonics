#!/usr/bin/env python3
"""Cold comparison of recorded-temporal continuation checkpoints and reports."""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import struct
import wave

from compare_recorded_temporal_action import resident_point, toward_zero, convolve


CHECKPOINT_MAGIC = b"HNA-CONDITIONAL-FIELD\x01"
CHECKPOINT_END = b"HNA-CONDITIONAL-FIELD-END\x01"
SECTION_MAGIC = b"HRSRST\0\x01"
RELATION_MAGIC = b"HNA-CONSTITUTIVE-FIBRE-REST\x01"
RELATION_END = b"HNA-CONSTITUTIVE-FIBRE-END\x01"
CONDITION_MAGIC = b"HNA-CONDITION-CURRENT-REST\x01"
CONDITION_END = b"HNA-CONDITION-CURRENT-END\x01"
FIELD_MAGIC = b"HNA-NATIVE-FIELD-REST\x01"
FIELD_END = b"HNA-NATIVE-FIELD-END\x01"
PCM_DIVISOR = 32768
PCM_GAIN = 8192


def fail(message):
    raise ValueError(message)


def blob(data, at, end):
    if at + 8 > end:
        fail("truncated blob length")
    length = struct.unpack_from("<Q", data, at)[0]
    at += 8
    if length > end - at:
        fail("blob exceeds containing extent")
    until = at + length
    return data[at:until], until


def json_blob(data, at, end):
    raw, at = blob(data, at, end)
    try:
        return json.loads(raw), at
    except json.JSONDecodeError as error:
        fail(f"malformed JSON blob: {error}")


def parse_rest_wire(raw, magic, end_marker):
    if not raw.startswith(magic):
        fail("native rest magic")
    end = len(raw)
    header, at = json_blob(raw, len(magic), end)
    section, at = blob(raw, at, end)
    if not section.startswith(SECTION_MAGIC):
        fail("native rest section carrier")
    if raw[at:] != end_marker:
        fail("native rest end marker or trailing bytes")
    return {"raw": raw, "header": header, "section": section}


def point_bytes(raw):
    if len(raw) < 24:
        fail("short field point carrier")
    rows, width, population = struct.unpack_from("<QQQ", raw, 0)
    if rows == 0 or width == 0 or rows * width != population:
        fail("field point shape")
    if len(raw) != 24 + 8 * population:
        fail("field point extent")
    return rows, width, population


def field_incoming(raw, nodes):
    if point_bytes(raw) != (nodes, 3, 3 * nodes):
        fail("field input must retain normalized per-node phase triples")
    triples = list(struct.iter_unpack("<qqq", raw[24:]))
    if any(d <= 0 for _, _, d in triples):
        fail("field input denominator")
    return [q for r, i, d in triples for q in (Q(r, d), Q(i, d))]


def parse_field_rest(raw):
    if not raw.startswith(FIELD_MAGIC):
        fail("field rest magic")
    end = len(raw)
    header, at = json_blob(raw, len(FIELD_MAGIC), end)

    def section():
        nonlocal at
        value, at = blob(raw, at, end)
        point_bytes(value)
        return value

    standing_sections = [section(), section(), section()]
    if header.get("junction") is not None:
        standing_sections.append(section())
    if header.get("junction") is not None and not header.get("history"):
        standing_sections.append(section())
    if header.get("transport"):
        standing_sections.append(section())
    history_sections = []
    for event in header.get("history", []):
        event_sections = [section()]
        if header.get("junction") is not None:
            event_sections.append(section())
        if header.get("transport"):
            event_sections.append(section())
        incoming = event.get("lineage", {}).get("incoming")
        if isinstance(incoming, dict) and "resident_nodes" in incoming:
            event_sections.append(section())
        history_sections.append(event_sections)
    if raw[at:] != FIELD_END:
        fail("field rest end marker or trailing bytes")
    return {"raw": raw, "header": header,
            "standing_sections": standing_sections,
            "history_sections": history_sections}


def parse_transport(data, at, end):
    header_raw, at = blob(data, at, end)
    input_raw, at = blob(data, at, end)
    output_raw, at = blob(data, at, end)
    try:
        header = json.loads(header_raw)
    except json.JSONDecodeError as error:
        fail(f"malformed transport header: {error}")
    required = {"sequence", "input_complete", "output_accepted", "closed", "has_output"}
    if set(header) != required or not isinstance(header["has_output"], bool):
        fail("transport header fields")
    if not header["has_output"] and output_raw:
        fail("unclaimed transport output")
    return {
        "header": header,
        "header_raw": header_raw,
        "input_raw": input_raw,
        "output_raw": output_raw,
        "raw": (header_raw, input_raw, output_raw),
    }, at


def parse_checkpoint(path):
    path = Path(path)
    data = path.read_bytes()
    minimum = len(CHECKPOINT_MAGIC) + len(CHECKPOINT_END) + 32 + 8
    if len(data) < minimum:
        fail("checkpoint minimum extent")
    footer = len(data) - len(CHECKPOINT_END) - 32
    expected = data[footer:footer + 32]
    if data[footer + 32:] != CHECKPOINT_END:
        fail("checkpoint footer marker")
    if hashlib.sha256(data[:footer]).digest() != expected:
        fail("checkpoint checksum")
    if not data.startswith(CHECKPOINT_MAGIC):
        fail("checkpoint magic/version")
    at = len(CHECKPOINT_MAGIC)
    transport, at = parse_transport(data, at, footer)
    application_raw, at = blob(data, at, footer)
    try:
        application = json.loads(application_raw)
    except json.JSONDecodeError as error:
        fail(f"checkpoint application JSON: {error}")
    if at + 8 > footer:
        fail("checkpoint native extent")
    native_extent = struct.unpack_from("<Q", data, at)[0]
    at += 8
    native_end = at + native_extent
    if native_end != footer:
        fail("checkpoint native extent does not reach footer")
    relation_raw, at = blob(data, at, native_end)
    condition_raw, at = blob(data, at, native_end)
    field_raw, at = blob(data, at, native_end)
    if at != native_end:
        fail("checkpoint native component trailing bytes")
    return {
        "path": path,
        "bytes": data,
        "transport": transport,
        "application_raw": application_raw,
        "application": application,
        "relation": parse_rest_wire(relation_raw, RELATION_MAGIC, RELATION_END),
        "condition": parse_rest_wire(condition_raw, CONDITION_MAGIC, CONDITION_END),
        "field": parse_field_rest(field_raw),
    }


def read_mono_pcm(path):
    path = Path(path)
    raw = path.read_bytes()
    with wave.open(str(path), "rb") as recording:
        if recording.getnchannels() != 1 or recording.getsampwidth() != 2:
            fail("continuation source must be mono PCM16")
        rate = recording.getframerate()
        frames = recording.getnframes()
        samples = struct.unpack(f"<{frames}h", recording.readframes(frames))
    return path, raw, rate, frames, samples


def verify_source(report):
    source = report.get("source")
    if not isinstance(source, dict):
        fail("missing continuation source")
    path, raw, rate, frames, samples = read_mono_pcm(source["path"])
    if source["sha256"] != hashlib.sha256(raw).hexdigest() or source["octets"] != len(raw):
        fail("continuation source hash or extent")
    if source["samples"] != frames or source["sample_rate"] != rate:
        fail("continuation source clock or frame count")
    return path, rate, frames, samples


def condition_successor(condition):
    header = condition["header"]
    width = header.get("width")
    if not isinstance(width, int) or width <= 0 or width % 2:
        fail("condition rest width")
    section = condition["section"]
    rows, stored_width, grain, bound, population = struct.unpack_from("<QQIIQ", section, 8)
    if rows != 1 or stored_width != 5 * width + 2 or grain != 0 or bound != 64:
        fail("condition rest section shape")
    if population != stored_width or len(section) != 40 + 16 * population:
        fail("condition rest section extent")
    words = [struct.unpack_from("<qq", section, 40 + 16 * i)[0] for i in range(population)]
    if any(struct.unpack_from("<qq", section, 40 + 16 * i)[0] !=
           struct.unpack_from("<qq", section, 40 + 16 * i)[1] for i in range(population)):
        fail("condition rest interval")
    denominator = words[5 * width]
    if denominator <= 0:
        fail("condition rest denominator")
    return [Q(words[width + i], denominator) for i in range(width)]


def verify_field_transition(previous, current):
    before_wire = previous["field"]
    after_wire = current["field"]
    before = before_wire["header"]
    after = after_wire["header"]
    old_history = before.get("history", [])
    new_history = after.get("history", [])
    if len(new_history) != len(old_history) + 1:
        fail("field occurrence continuation")
    for key in ("nodes", "material", "frames", "recharts", "changes", "junction",
                "transport", "transport_source"):
        if before.get(key) != after.get(key):
            fail(f"field standing changed: {key}")
    if before_wire["standing_sections"][0] != after_wire["standing_sections"][0]:
        fail("field seed changed")
    old_slots = before.get("source_slots")
    new_slots = after.get("source_slots")
    if not isinstance(old_slots, list) or not isinstance(new_slots, list) or len(old_slots) != 1 or len(new_slots) != 1:
        fail("field source slots")
    source_at = old_slots[0]
    if not isinstance(source_at, int) or new_slots[0] != len(old_history):
        fail("field source slot did not advance to new occurrence")
    for at, (old, new) in enumerate(zip(old_history, new_history)):
        expected = deepcopy(old)
        if at == source_at:
            if old.get("returned") is not False or new.get("returned") is not True:
                fail("consumed saved source chronology")
            expected["returned"] = True
        if new != expected:
            fail("field history prefix changed")
    if after_wire["history_sections"][:len(old_history)] != before_wire["history_sections"]:
        fail("field history carrier prefix changed")
    # The moment is developing standing: this new joined contact must add d d*.
    # Only this experiment's unchanged unit root frame is admitted by this observer.
    n = before["nodes"]
    unit = {"real": 1, "imaginary": 0, "denominator": 1}
    if before["frames"] != [{"ordinal": 0, "root_to_local": [unit] * n}]:
        fail("observer requires the declared unit root frame")
    def words(raw):
        _, _, population = point_bytes(raw)
        return list(struct.unpack_from(f"<{population}q", raw, 24))
    source = words(before_wire["history_sections"][source_at][0])
    arrival = field_incoming(after_wire["history_sections"][-1][-1], n)
    if source[4*n] <= 0:
        fail("field contact denominator")
    d = [Q(v, source[4*n]) for v in source[:4*n]] + [-v for v in arrival]
    jd = [v for i in range(3*n) for v in (-d[2*i+1], d[2*i])]
    old_cov = words(before_wire["standing_sections"][3])
    new_cov = words(after_wire["standing_sections"][3])
    dim = 6*n
    if len(old_cov) != dim*dim+1 or len(new_cov) != dim*dim+1 or min(old_cov[-1], new_cov[-1]) <= 0:
        fail("field moment shape")
    if any(Q(new_cov[i*dim+j], new_cov[-1]) != Q(old_cov[i*dim+j], old_cov[-1]) + d[i]*d[j] + jd[i]*jd[j]
           for i in range(dim) for j in range(dim)):
        fail("field joined-contact moment update")
    latest = new_history[-1].get("lineage", {})
    prior = old_history[-1].get("lineage", {})
    if (latest.get("occurrence") != len(old_history)
            or latest.get("received_from") != source_at
            or latest.get("predecessor_state") != source_at
            or latest.get("frame") != prior.get("frame")):
        fail("new field lineage chronology")
    if after.get("anchor_slots") != before.get("anchor_slots"):
        fail("field anchors changed")
    return {"prior_occurrences": len(old_history), "occurrences": len(new_history),
            "consumed_source": source_at, "new_source": new_slots[0],
            "history_prefix_retained": True, "joined_contact_moment_verified": True}


def verify_report(path):
    report_path = Path(path)
    report = json.loads(report_path.read_text())
    if report.get("schema") != "holonics.recorded-temporal-continuation.v1":
        fail("continuation report schema")
    source_path, rate, count, samples = verify_source(report)
    predecessor_path = Path(report["predecessor_checkpoint"])
    current_path = Path(report["checkpoint"]["path"])
    predecessor = parse_checkpoint(predecessor_path)
    current = parse_checkpoint(current_path)
    if report.get("predecessor_application") != predecessor["application"]:
        fail("predecessor application differs from checkpoint")
    before_app = predecessor["application"]
    after_app = current["application"]
    if after_app.get("schema") != "holonics.recorded-temporal-continuation.v1":
        fail("current application schema")
    required_chart = {"source_complex": 4, "response_complex": 2, "phase_extent": 4,
                      "pcm_divisor": PCM_DIVISOR, "pcm_gain": PCM_GAIN}
    for application in (before_app, after_app):
        if application.get("schema") != "holonics.recorded-temporal-continuation.v1":
            fail("checkpoint application schema")
        for key, expected in required_chart.items():
            if application.get(key) != expected:
                fail(f"application chart field: {key}")
    for key in (*required_chart, "sample_rate"):
        if after_app.get(key) != before_app.get(key):
            fail(f"application chart changed: {key}")
    if after_app.get("completed_recordings") != before_app.get("completed_recordings", 0) + 1:
        fail("application recording chronology")
    if after_app.get("last_source") != report["source"]:
        fail("application last source differs from report source")
    if after_app.get("sample_rate") != rate:
        fail("application/source sample clock")
    if report["source"].get("receiver") != 1 \
            or report["source"].get("lineage") != after_app.get("completed_recordings"):
        fail("continuation source lineage")
    if predecessor["transport"]["raw"] != current["transport"]["raw"]:
        fail("transport changed across continuation")

    relation_before = predecessor["relation"]
    relation_after = current["relation"]
    before_relation_keys = set(relation_before["header"]) - {"occurrences"}
    after_relation_keys = set(relation_after["header"]) - {"occurrences"}
    if before_relation_keys != after_relation_keys:
        fail("relation header fields changed")
    for key in before_relation_keys:
        if relation_after["header"].get(key) != relation_before["header"].get(key):
            fail(f"relation header changed: {key}")
    if relation_before["section"] != relation_after["section"]:
        fail("relation basis changed")
    if relation_after["header"].get("occurrences") != relation_before["header"].get("occurrences", 0) + 1:
        fail("relation occurrence chronology")
    condition_before = predecessor["condition"]
    condition_after = current["condition"]
    if condition_before["raw"] != condition_after["raw"]:
        fail("condition current changed across continuation")
    if condition_after["header"].get("contacts") != condition_before["header"].get("contacts"):
        fail("condition contact count changed")
    field_transition = verify_field_transition(predecessor, current)

    relation_report = report.get("relation", {})
    if relation_report.get("prior_occurrences") != relation_before["header"].get("occurrences") \
            or relation_report.get("occurrences") != relation_after["header"].get("occurrences") \
            or relation_report.get("prior_contacts") != condition_before["header"].get("contacts") \
            or relation_report.get("contacts") != condition_after["header"].get("contacts"):
        fail("reported relation chronology")
    native_field = report.get("native_field", {})
    if native_field.get("prior_occurrences") != field_transition["prior_occurrences"] \
            or native_field.get("occurrences") != field_transition["occurrences"]:
        fail("reported field chronology")
    if native_field.get("lineage") != current["field"]["header"]["history"][-1]["lineage"]:
        fail("reported newest field lineage")

    stages = report.get("stages", {})
    for name in ("cold_remount", "resident_relation_and_field", "whole_recording_mount",
                 "whole_recording_successor_condition"):
        stage = stages.get(name)
        if stage is None or stage.get("section_readouts") != 0 \
                or stage.get("numerical_egress_octets") != 0:
            fail(f"native stage egress: {name}")
    if stages["cold_remount"].get("deeds") != 0:
        fail("cold remount replayed native deeds")
    terminal = stages.get("cold_terminal_receiver", {})
    expected_egress = 16 * (2 * (count + 1) + 1)
    if terminal.get("section_readouts") != 1 or terminal.get("numerical_egress_octets") != expected_egress:
        fail("continuation terminal receiver egress")

    whole = report.get("whole_recording", {})
    if whole.get("source_raw_extent") != count or whole.get("response_raw_extent") != 2 \
            or whole.get("output_raw_extent") != count + 1 or whole.get("gain") != str(PCM_GAIN):
        fail("whole recording extent or gain")
    projection = whole.get("successor_condition")
    if projection is None or projection.get("receiver") != 5 \
            or projection.get("lineage") != after_app.get("completed_recordings") \
            or projection.get("origin") != "0" or projection.get("sample_step") != f"1/{rate}" \
            or projection.get("sample_rate") != rate or projection.get("frames") != count + 1:
        fail("successor projection metadata")
    section_path = Path(projection["section_path"])
    wav_path = Path(projection["wav_path"])
    if not section_path.is_absolute() or not wav_path.is_absolute():
        fail("projection paths are not absolute")
    section_bytes = section_path.read_bytes()
    wav_bytes = wav_path.read_bytes()
    if hashlib.sha256(section_bytes).hexdigest() != projection["section_sha256"] \
            or hashlib.sha256(wav_bytes).hexdigest() != projection["wav_sha256"]:
        fail("projection hash")
    condition = condition_successor(condition_after)
    short_source = [q for sample in samples[:4] for q in (Q(sample, PCM_DIVISOR), Q(0))]
    expected_short = convolve(short_source, condition)
    bounded = report.get("bounded_prediction")
    if not isinstance(bounded, dict) or bounded.get("status") != "unique" \
            or [Q(value) for value in bounded.get("coordinates", [])] != expected_short:
        fail("bounded prediction differs from saved condition convolution")
    history_sections = current["field"]["history_sections"]
    if not history_sections:
        fail("missing current field history carrier")
    incoming = history_sections[-1][-1]
    if field_incoming(incoming, len(expected_short) // 2) != expected_short:
        fail("latest resident input differs from bounded prediction")
    source = [q for sample in samples for q in (Q(sample, PCM_DIVISOR), Q(0))]
    expected = convolve(source, condition)
    coordinates, section_meta = resident_point(section_path, 2 * (count + 1) + 1)
    if coordinates != expected:
        fail("successor exact full-recording convolution")
    with wave.open(str(wav_path), "rb") as recording:
        if recording.getnchannels() != 2 or recording.getsampwidth() != 2 \
                or recording.getframerate() != rate or recording.getnframes() != count + 1:
            fail("successor PCM clock or extent")
        pcm = struct.unpack(f"<{2 * (count + 1)}h", recording.readframes(count + 1))
    clipped = 0
    for real, imaginary, left, right in zip(coordinates[::2], coordinates[1::2], pcm[::2], pcm[1::2]):
        for value, sample in ((real, left), (imaginary, right)):
            scaled = value * PCM_GAIN
            unbounded = toward_zero(scaled)
            bounded = max(-32768, min(32767, unbounded))
            if sample != bounded:
                fail("successor PCM quantization")
            clipped += int(unbounded != bounded)
            remainder = scaled - Q(sample)
            if (Q(sample) + remainder) / PCM_GAIN != value:
                fail("successor quantization remainder")
    if clipped != projection.get("clipped_sample_population"):
        fail("successor clipped population")

    return {
        "report": str(report_path),
        "predecessor_checkpoint": str(predecessor_path),
        "checkpoint": str(current_path),
        "source_sha256": report["source"]["sha256"],
        "sample_rate": rate,
        "completed_recordings": after_app["completed_recordings"],
        "relation_basis_unchanged": True,
        "condition_rest_unchanged": True,
        "transport_unchanged": True,
        "field": field_transition,
        "native_stages_zero_egress": True,
        "cold_remount_zero_deeds": True,
        "whole_recording_exact_convolution": True,
        "latest_resident_input_matches_bounded_prediction": True,
        "pcm_gain_clock_tail_remainders_verified": True,
        "projection_section_sha256": projection["section_sha256"],
        "projection_wav_sha256": projection["wav_sha256"],
        "section": section_meta,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", type=Path, nargs="+")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        fail(f"output already exists: {args.output}")
    result = {
        "truth_status": "established-bounded",
        "evidence_tags": ["measured"],
        "scope": "cold continuation checkpoint and exact controlled digital action comparison; no semantic claim",
        "comparisons": [verify_report(path) for path in args.reports],
    }
    with args.output.open("x") as output:
        json.dump(result, output, indent=2)
        output.write("\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
