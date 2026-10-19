#!/usr/bin/env python3
"""Frame REQ-20261018-064 from explicit, hash-pinned local train inputs.

Usage: python3 tools/listener/micro.py --inputs inputs.json --out-dir .local/micro

The inputs JSON has `gsm8k`, `mnist_images`, `mnist_labels`, and `librispeech`
(exactly three entries). Every entry supplies path, sha256, dataset and split.
GSM8K's split is train and filename train.jsonl; MNIST's split is train and its
filenames are train-images-idx3-ubyte / train-labels-idx1-ubyte (optionally .gz).
LibriSpeech entries also supply utterance_id and live at
<train-clean-100|train-clean-360|train-other-500>/<speaker>/<chapter>/<id>.flac
(a pinned mono i16 WAV derivative with the same identity is also accepted).
Paths resolve relative to inputs.json. Names and structure validate the declared
identity; they do not establish semantic authenticity of arbitrary renamed bytes.

If a recording starts with zeros, inputs must explicitly declare
`leading_silence: "count_as_run"`; otherwise the H-count convention is unresolved.
No data is fetched, no package is installed, and no learner is run. The exact
boundary fibres are emitted beside the stream in its private .local manifest.
"""

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import wave


MAGIC = b"HLSN1\n"
ORDER = ("text", "digit", "sound", "text", "digit", "sound", "text", "digit", "sound", "text")
TRAIN_SPLITS = {"train-clean-100", "train-clean-360", "train-other-500"}
DIRECTIONS = ((0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1))
TURNS = (0, 1, 7, 2, 6, 3, 5, 4)


class Refusal(ValueError):
    """A malformed input, unavailable decoder, or unresolved exterior convention."""


def digest(data):
    return hashlib.sha256(data).hexdigest()


def cells(octets):
    """Cell count including exactly one framing end letter, not a chart sample."""
    return 2 * len(octets) + 2


def stroke(width, height, intensities):
    """Same row-down clockwise eighth-turn chart as listener/sections.rs."""
    if len(intensities) != width * height or not 0 <= width <= 65535 or not 0 <= height <= 65535 or any(not 0 <= value <= 255 for value in intensities):
        raise Refusal("raster dimensions and intensities differ")
    visited = set()
    octets, remainders = bytearray(), []
    row = col = heading = next_pixel = jumps = 0
    pen_down = False
    while True:
        found = None
        if pen_down:
            for turn in TURNS:
                direction = (heading + turn) % 8
                dr, dc = DIRECTIONS[direction]
                r, c = row + dr, col + dc
                index = r * width + c
                if 0 <= r < height and 0 <= c < width and index not in visited and intensities[index]:
                    found = index, r, c, turn, direction
                    break
        if found is None:
            while next_pixel < len(intensities) and (next_pixel in visited or not intensities[next_pixel]):
                next_pixel += 1
            if next_pixel == len(intensities):
                break
            r, c = divmod(next_pixel, width)
            found = next_pixel, r, c, 8, 0
        index, r, c, turn, direction = found
        value = intensities[index]
        octave = value.bit_length() - 1
        octets.append((turn << 4) | octave)
        if turn == 8:
            dr, dc = r - row, c - col
            if not (-128 <= dr <= 127 and -128 <= dc <= 127):
                raise Refusal(f"stroke signed jump overflow: row={dr} column={dc}")
            octets.extend(struct.pack("bb", dr, dc))
            jumps += 1
        remainders.append(value - (1 << octave))
        visited.add(index)
        row, col, heading, pen_down = r, c, direction, True
    return bytes(octets), {"width": width, "height": height, "jumps": jumps, "remainders": remainders}


def decode_stroke(octets, fibre):
    """Read the complete raster from the declared zero background and pixel remainders."""
    width, height = fibre["width"], fibre["height"]
    if not 0 <= width <= 65535 or not 0 <= height <= 65535:
        raise Refusal("invalid stroke frame")
    pixels = bytearray(width * height)
    at = index = row = col = heading = 0
    while at < len(octets):
        turn, octave = divmod(octets[at], 16)
        at += 1
        if turn > 8 or octave > 7 or (index == 0 and turn != 8):
            raise Refusal("invalid stroke turn or octave")
        if turn == 8:
            if at + 2 > len(octets):
                raise Refusal("truncated stroke jump")
            dr, dc = struct.unpack("bb", octets[at:at + 2])
            at += 2
            row, col, heading = row + dr, col + dc, 0
        else:
            heading = (heading + turn) % 8
            dr, dc = DIRECTIONS[heading]
            row, col = row + dr, col + dc
        if not (0 <= row < height and 0 <= col < width) or index >= len(fibre["remainders"]):
            raise Refusal("stroke landing outside frame or missing fibre")
        remainder = fibre["remainders"][index]
        position = row * width + col
        if pixels[position] or not 0 <= remainder < (1 << octave):
            raise Refusal("revisited pixel or invalid intensity fibre")
        pixels[position] = (1 << octave) + remainder
        index += 1
    if index != len(fibre["remainders"]) or stroke(width, height, pixels) != (bytes(octets), fibre):
        raise Refusal("noncanonical stroke chart/fibre")
    return bytes(pixels)


def sign(sample):
    return 0 if sample > 0 else 1 if sample < 0 else 2


def runs_of(samples):
    """Runs include a leading silent run; zeros thereafter continue the current sign."""
    at, runs = 0, []
    while at < len(samples):
        orientation = sign(samples[at])
        end = at + 1
        while end < len(samples) and (sign(samples[end]) == orientation or (orientation != 2 and samples[end] == 0)):
            end += 1
        runs.append((at, end, orientation))
        at = end
    return runs


def half_cycles(rate, samples):
    if not 0 < rate <= 0xFFFFFFFF or any(not -32768 <= sample <= 32767 for sample in samples):
        raise Refusal("PCM requires a positive u32 rate and i16 samples")
    octets, fibres = bytearray(), []
    for at, end, orientation in runs_of(samples):
        peak = max(abs(sample) for sample in samples[at:end])
        octave = peak.bit_length() - 1 if peak else 0
        remainder = peak - (1 << octave) if peak else 0
        signed_peak = -peak if orientation == 1 else peak
        length = end - at
        octets.extend(b"\xff" * (length // 255))
        octets.extend((length % 255, (orientation << 4) | octave))
        fibres.append({"peak_remainder": remainder, "samples_from_peak": [sample - signed_peak for sample in samples[at:end]]})
    return bytes(octets), {"rate": rate, "runs": fibres}


def decode_half_cycles(octets, fibre):
    """Independent read-back from length, signed peak and exact sample residuals."""
    at, output = 0, []
    for run in fibre["runs"]:
        length = 0
        while True:
            if at >= len(octets):
                raise Refusal("unterminated half-cycle length")
            part = octets[at]
            at += 1
            length += part
            if part != 255:
                break
        if at >= len(octets):
            raise Refusal("missing half-cycle peak")
        orientation, octave = divmod(octets[at], 16)
        at += 1
        remainder = run["peak_remainder"]
        if not length or length != len(run["samples_from_peak"]) or orientation > 2 or not 0 <= remainder < (1 << octave):
            raise Refusal("invalid half-cycle fibre")
        if orientation == 2 and (octave or remainder):
            raise Refusal("invalid silent peak")
        peak = 0 if orientation == 2 else (1 << octave) + remainder
        if orientation == 1:
            peak = -peak
        for residual in run["samples_from_peak"]:
            sample = peak + residual
            if not -32768 <= sample <= 32767:
                raise Refusal("decoded sample exceeds i16")
            output.append(sample)
    if at != len(octets) or half_cycles(fibre["rate"], output) != (bytes(octets), fibre):
        raise Refusal("noncanonical half-cycle chart/fibre")
    return output


def split_first_span(answer):
    start = answer.find("<<")
    end = answer.find(">>", start + 2) if start >= 0 else -1
    span = answer[start + 2:end] if end >= 0 else ""
    if start < 0 or end < 0 or "<" in span or ">" in span or span.count("=") != 1:
        raise Refusal("first GSM8K annotation must contain exactly one equals sign")
    expression, target = span.split("=", 1)
    if not expression or not target:
        raise Refusal("empty GSM8K expression or target")
    return (expression + "=").encode("utf-8"), target.encode("utf-8")


def pinned(spec, dataset, split, base):
    if not isinstance(spec, dict) or spec.get("dataset") != dataset or spec.get("split") != split:
        raise Refusal(f"expected explicit {dataset} {split} identity")
    expected = spec.get("sha256", "")
    if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
        raise Refusal("each input needs its pinned lowercase SHA256")
    path = (base / spec.get("path", "")).resolve()
    raw = path.read_bytes()
    if digest(raw) != expected:
        raise Refusal(f"input hash differs: {path.name}")
    identity = {"dataset": dataset, "split": split, "filename": path.name, "sha256": expected, "file_bytes": len(raw)}
    return path, raw, identity


def idx_inputs(image_raw, label_raw):
    if len(image_raw) < 16 or len(label_raw) < 8:
        raise Refusal("truncated MNIST header")
    magic, count, height, width = struct.unpack(">4I", image_raw[:16])
    label_magic, label_count = struct.unpack(">2I", label_raw[:8])
    if magic != 2051 or label_magic != 2049 or count != label_count or count < 3:
        raise Refusal("MNIST image/label headers differ or have fewer than three items")
    if not 0 < width <= 65535 or not 0 < height <= 65535 or len(image_raw) != 16 + count * width * height or len(label_raw) != 8 + count:
        raise Refusal("MNIST extent differs from its header")
    if any(label > 9 for label in label_raw[8:]):
        raise Refusal("MNIST label is not a numeral")
    return [(width, height, image_raw[16 + i * width * height:16 + (i + 1) * width * height], bytes([ord("0") + label_raw[8 + i]])) for i in range(3)]


def wav_pcm(raw):
    try:
        with wave.open(io.BytesIO(raw), "rb") as source:
            if source.getnchannels() != 1 or source.getsampwidth() != 2 or source.getcomptype() != "NONE":
                raise Refusal("sound input must already be mono, uncompressed 16-bit PCM; no resampling or channel conversion")
            rate, count = source.getframerate(), source.getnframes()
            payload = source.readframes(count)
    except (wave.Error, EOFError) as error:
        raise Refusal(f"invalid WAV: {error}") from error
    if len(payload) != 2 * count:
        raise Refusal("truncated WAV sample payload")
    return rate, list(struct.unpack(f"<{count}h", payload))


def audio_input(path, raw):
    if path.suffix.lower() == ".wav":
        rate, samples = wav_pcm(raw)
        return rate, samples, {"tool": "python.wave", "python": sys.version.split()[0], "conversion": "none"}
    if path.suffix.lower() != ".flac":
        raise Refusal("sound source must be pinned FLAC or a pinned WAV derivative")
    decoder = shutil.which("flac")
    if decoder is None:
        raise Refusal("FLAC decoder missing; nothing was installed or fetched")
    version = subprocess.run([decoder, "--version"], check=True, capture_output=True, text=True).stdout.strip()
    decoded = subprocess.run([decoder, "--decode", "--stdout", "--silent", "-"], input=raw, check=True, capture_output=True).stdout
    rate, samples = wav_pcm(decoded)
    return rate, samples, {"tool": "flac", "version": version, "decoded_wav_sha256": digest(decoded), "conversion": "lossless decode only"}


def sound_identity(spec, path):
    utterance = spec.get("utterance_id", "")
    match = re.fullmatch(r"([0-9]+)-([0-9]+)-([0-9]+)", utterance)
    if match is None or path.stem != utterance or spec.get("split") not in TRAIN_SPLITS:
        raise Refusal("LibriSpeech needs its explicit train split and matching utterance identity")
    speaker, chapter, _ = match.groups()
    if path.parent.name != chapter or path.parent.parent.name != speaker or path.parent.parent.parent.name != spec["split"]:
        raise Refusal("LibriSpeech train/speaker/chapter path differs from its declared identity")
    return utterance


def fragment(rate, samples, digit_source_cells, silence_policy=None):
    runs = runs_of(samples)
    if runs and runs[0][2] == 2 and silence_policy != "count_as_run":
        raise Refusal("unresolved: leading silent run's H-count convention; declare leading_silence=count_as_run")
    best, candidate_costs = None, []
    for h in range(1, (len(runs) - 1) // 2 + 1):
        # Both cuts have a following run and must be actual signed crossings, never EOF/silence.
        if runs[h - 1][2] == 2 or runs[2 * h - 1][2] == 2:
            continue
        cut, end = runs[h - 1][1], runs[2 * h - 1][1]
        source, target = half_cycles(rate, samples[:cut]), half_cycles(rate, samples[cut:end])
        total = cells(source[0]) + cells(target[0])
        candidate_costs.append({"H": h, "combined_cells": total})
        if total <= digit_source_cells:
            best = h, cut, end, source, target
        else:
            break
    if best is None:
        raise Refusal("no complete H/H fragment fits the digit source cells at two sign-change cuts")
    h, cut, end, source, target = best
    whole = half_cycles(rate, samples[:end])
    if whole[0] != source[0] + target[0] or decode_half_cycles(*source) != samples[:cut] or decode_half_cycles(*target) != samples[cut:end]:
        raise Refusal("half-cycle composition or exact decode failed")
    metadata = {"H": h, "source_sample_range": [0, cut], "target_sample_range": [cut, end], "source_chart_octets": len(source[0]), "target_chart_octets": len(target[0]), "source_cells": cells(source[0]), "target_cells": cells(target[0]), "combined_cells": cells(source[0]) + cells(target[0]), "digit_source_cell_bound": digit_source_cells, "candidate_costs": candidate_costs, "source_fibre": source[1], "target_fibre": target[1], "source_chart_sha256": digest(source[0]), "target_chart_sha256": digest(target[0]), "fragment_i16be_sha256": digest(struct.pack(f">{end}h", *samples[:end])), "whole_chart_sha256": digest(whole[0]), "whole_chart_is_source_plus_target": True, "cuts_are_sign_changes": True, "leading_silence": silence_policy if runs[0][2] == 2 else "absent"}
    return samples[:cut], target[0], metadata


def frame_octets(source, target):
    return struct.pack(">IBI", 1, 0, len(source)) + source + struct.pack(">I", len(target)) + target


def frame_raster(width, height, intensities, target):
    return struct.pack(">IBHH", 1, 1, width, height) + intensities + struct.pack(">I", len(target)) + target


def frame_pcm(rate, samples, target):
    return struct.pack(">IBII", 1, 2, rate, len(samples)) + struct.pack(f">{len(samples)}h", *samples) + struct.pack(">I", len(target)) + target


def build(config, base):
    if not isinstance(config, dict) or len(config.get("librispeech", [])) != 3:
        raise Refusal("exactly three explicit LibriSpeech train utterances are required")
    if config.get("leading_silence") not in (None, "count_as_run"):
        raise Refusal("unsupported leading_silence convention")
    gsm_path, gsm_raw, gsm_identity = pinned(config["gsm8k"], "GSM8K", "train", base)
    if gsm_path.name != "train.jsonl":
        raise Refusal("GSM8K requires the explicitly pinned train.jsonl")
    lines = gsm_raw.splitlines()
    if len(lines) < 4:
        raise Refusal("GSM8K has fewer than four train rows")
    texts = [split_first_span(json.loads(line)["answer"]) for line in lines[:4]]
    image_path, image_raw, image_identity = pinned(config["mnist_images"], "MNIST", "train", base)
    label_path, label_raw, label_identity = pinned(config["mnist_labels"], "MNIST", "train", base)
    for path, expected in [(image_path, "train-images-idx3-ubyte"), (label_path, "train-labels-idx1-ubyte")]:
        if path.name not in (expected, expected + ".gz"):
            raise Refusal("MNIST requires explicitly named train IDX files")
    image_data = gzip.decompress(image_raw) if image_path.suffix == ".gz" else image_raw
    label_data = gzip.decompress(label_raw) if label_path.suffix == ".gz" else label_raw
    digits = idx_inputs(image_data, label_data)
    digit_charts = [stroke(width, height, pixels) for width, height, pixels, _ in digits]
    if any(decode_stroke(*chart) != digit[2] for digit, chart in zip(digits, digit_charts)):
        raise Refusal("digit chart failed exact reconstruction")
    sounds, sound_identities = [], []
    for i, spec in enumerate(config["librispeech"]):
        split = spec.get("split")
        if split not in TRAIN_SPLITS:
            raise Refusal("LibriSpeech split must name an actual train partition")
        path, raw, identity = pinned(spec, "LibriSpeech", split, base)
        identity["utterance_id"] = sound_identity(spec, path)
        if identity["utterance_id"] in [entry["utterance_id"] for entry in sound_identities]:
            raise Refusal("three distinct LibriSpeech train utterances are required")
        rate, samples, decoder = audio_input(path, raw)
        pcm_payload = struct.pack(f">{len(samples)}h", *samples)
        identity.update({"decoder": decoder, "pcm_rate": rate, "pcm_samples": len(samples), "pcm_i16be_sha256": digest(pcm_payload)})
        source, target, metadata = fragment(rate, samples, cells(digit_charts[i][0]), config.get("leading_silence"))
        sounds.append((frame_pcm(rate, source, target), metadata))
        sound_identities.append(identity)
    frames, items = [], []
    counters = {"text": 0, "digit": 0, "sound": 0}
    for kind in ORDER:
        i = counters[kind]
        counters[kind] += 1
        item = {"round": len(items), "chart": kind, "train_index": i}
        if kind == "text":
            source, target = texts[i]
            framed = frame_octets(source, target)
            item.update({"source_octets": len(source), "target_octets": len(target), "source_cells": cells(source), "target_cells": cells(target), "source_sha256": digest(source), "target_sha256": digest(target), "split_rule": "first annotation contents, source through its only equals sign"})
        elif kind == "digit":
            width, height, pixels, target = digits[i]
            chart, fibre = digit_charts[i]
            framed = frame_raster(width, height, pixels, target)
            item.update({"source_chart_octets": len(chart), "source_cells": cells(chart), "target_cells": cells(target), "source_pixels_sha256": digest(pixels), "source_chart_sha256": digest(chart), "source_fibre": fibre, "target_sha256": digest(target)})
        else:
            framed, metadata = sounds[i]
            item.update(metadata)
            item["utterance_id"] = sound_identities[i]["utterance_id"]
        item["frame_sha256"] = digest(framed)
        item["frame_bytes"] = len(framed)
        frames.append(framed)
        items.append(item)
    block = b"".join(frames)
    stream = MAGIC + block * 3
    manifests = {"schema": "holonics.listener.micro.v1", "request": "REQ-20261018-064 with origin-jump correction", "identity_validation": "pinned hashes, declared train metadata and filename/path structure; no semantic authenticity claim", "sections": 30, "passes": 3, "one_life": True, "order_per_pass": list(ORDER), "pass_block_bytes": len(block), "pass_block_sha256": [digest(block)] * 3, "stream_sha256": digest(stream), "stream_bytes": len(stream), "inputs": {"gsm8k": gsm_identity, "mnist_images": image_identity, "mnist_labels": label_identity, "librispeech": sound_identities}, "items_per_pass": items, "delivered_cells_per_pass": sum(item["source_cells"] + item["target_cells"] for item in items), "jumps_per_pass": sum(fibre["jumps"] for _, fibre in digit_charts), "framing": "one HLSN1 header; each passage and nonempty target has its own two-cell end letter", "composition_invariant": "raw PCM chart octets concatenate at signed crossings; passage end letters are not samples", "scientific_claim": "boundary framing only; no learner run or unseen-skill result"}
    manifests["delivered_cells_three_passes"] = 3 * manifests["delivered_cells_per_pass"]
    manifests["ordinal_accounting"] = "exact delivered source/target cells exclude runtime fork draws"
    manifests["request_rough_ordinal_estimate"] = {
        "constant_approximately": 7400,
        "jump_coefficient": 24,
        "J": manifests["jumps_per_pass"],
        "approximately": 7400 + 24 * manifests["jumps_per_pass"],
        "basis": "corrected mailbox estimate; exact stream cell counts above are authoritative",
    }
    return stream, manifests


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        out = args.out_dir.resolve()
        if ".local" not in out.parts:
            raise Refusal("stream and exact fibres must stay in a .local output directory")
        if out.exists():
            raise Refusal("output directory already exists; no artifacts were replaced")
        config = json.loads(args.inputs.read_text(encoding="utf-8"))
        stream, manifest = build(config, args.inputs.resolve().parent)
        manifest["inputs_manifest_sha256"] = digest(args.inputs.read_bytes())
        out.mkdir(parents=True, exist_ok=False)
        (out / "micro.hlsn").write_bytes(stream)
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps({"stream_sha256": manifest["stream_sha256"], "sections": 30, "delivered_cells_three_passes": manifest["delivered_cells_three_passes"], "jumps_per_pass": manifest["jumps_per_pass"]}, sort_keys=True))
        return 0
    except (Refusal, OSError, ValueError, KeyError, TypeError, OverflowError, struct.error, subprocess.SubprocessError) as error:
        print(f"micro framer refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
