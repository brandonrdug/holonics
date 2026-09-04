#!/usr/bin/env python3
"""Create the fixed, integer-addressed source for the contextual audio ecology cell."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

import numpy as np
import soundfile as sf
import torch
from transformers import WhisperForConditionalGeneration, WhisperProcessor


SCHEMA = "eros.audio-contextual-ecology.source.v1"
BLOCK_SAMPLES = 320
SAMPLE_RATE = 16_000

COMPONENTS = {
    "prefix": ("well", "en-us"),
    "quantity_left": ("I have", "en-us"),
    "pivot": ("two", "en-us"),
    "quantity_right": ("dogs", "en-us"),
    "degree_left": ("It is", "en-us"),
    "degree_right": ("loud", "en-us"),
    "direction_left": ("Walk", "en-us"),
    "direction_right": ("school", "en-us"),
    "held_pivot": ("two", "en-us+f3"),
}

TRAINING = [
    {
        "id": "quantity",
        "components": ["quantity_left", "pivot", "quantity_right"],
        "expected_text": " I have two dogs.",
    },
    {
        "id": "degree",
        "components": ["degree_left", "pivot", "degree_right"],
        "expected_text": " It is too loud.",
    },
    {
        "id": "direction",
        "components": ["direction_left", "pivot", "direction_right"],
        "expected_text": " Walk to school.",
    },
]

PROBES = [
    {
        "id": "quantity_local_nonidentity",
        "core": ["quantity_left", "pivot", "quantity_right"],
        "extras": ["prefix"],
        "expected_ecology": "quantity",
    },
    {
        "id": "degree_local_nonidentity",
        "core": ["degree_left", "pivot", "degree_right"],
        "extras": ["prefix"],
        "expected_ecology": "degree",
    },
    {
        "id": "direction_local_nonidentity",
        "core": ["direction_left", "pivot", "direction_right"],
        "extras": ["prefix"],
        "expected_ecology": "direction",
    },
    {
        "id": "changed_context",
        "core": ["quantity_left", "pivot", "degree_right"],
        "extras": [],
        "expected_ecology": None,
    },
    {
        "id": "reversed_chronology",
        "core": ["quantity_right", "pivot", "quantity_left"],
        "extras": [],
        "expected_ecology": None,
    },
    {
        "id": "held_speaker",
        "core": ["quantity_left", "held_pivot", "quantity_right"],
        "extras": [],
        "expected_ecology": None,
    },
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    return parser.parse_args()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def command_text(arguments: list[str]) -> str:
    return subprocess.run(
        arguments,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    ).stdout.strip()


def synthesize_component(
    identifier: str, text: str, voice: str, component_dir: Path, scratch: Path
) -> dict[str, Any]:
    native = scratch / f"{identifier}.wav"
    output = component_dir / f"{identifier}.wav"
    subprocess.run(
        ["espeak-ng", "-v", voice, "-s", "150", "-w", str(native), text],
        check=True,
    )
    subprocess.run(
        [
            "ffmpeg",
            "-hide_banner",
            "-loglevel",
            "error",
            "-i",
            str(native),
            "-map_metadata",
            "-1",
            "-ac",
            "1",
            "-ar",
            str(SAMPLE_RATE),
            "-c:a",
            "pcm_s16le",
            "-bitexact",
            str(output),
        ],
        check=True,
    )
    samples, rate = sf.read(output, dtype="int16")
    if rate != SAMPLE_RATE or samples.ndim != 1 or samples.size == 0:
        raise RuntimeError(f"{identifier} did not become nonempty mono 16 kHz PCM")
    blocks = []
    for ordinal, start in enumerate(range(0, samples.size, BLOCK_SAMPLES)):
        end = min(start + BLOCK_SAMPLES, samples.size)
        blocks.append(
            {
                "ordinal": ordinal,
                "start": start,
                "end": end,
                "sum": int(samples[start:end].astype(np.int64).sum()),
            }
        )
    return {
        "id": identifier,
        "text": text,
        "voice": voice,
        "path": str(output.resolve()),
        "sha256": sha256(output),
        "sample_rate": rate,
        "samples": int(samples.size),
        "blocks": blocks,
    }


def concatenate(
    identifier: str,
    component_ids: list[str],
    components: dict[str, dict[str, Any]],
    phrase_dir: Path,
) -> tuple[Path, np.ndarray, list[dict[str, Any]]]:
    arrays = []
    spans = []
    at = 0
    for role, component_id in enumerate(component_ids):
        samples, rate = sf.read(components[component_id]["path"], dtype="int16")
        if rate != SAMPLE_RATE or samples.ndim != 1:
            raise RuntimeError(f"{component_id} changed before phrase assembly")
        arrays.append(samples)
        spans.append(
            {
                "role": role,
                "component": component_id,
                "start": at,
                "end": at + int(samples.size),
            }
        )
        at += int(samples.size)
    joined = np.concatenate(arrays)
    path = phrase_dir / f"{identifier}.wav"
    sf.write(path, joined, SAMPLE_RATE, subtype="PCM_16")
    reread, rate = sf.read(path, dtype="int16")
    if rate != SAMPLE_RATE or not np.array_equal(joined, reread):
        raise RuntimeError(f"{identifier} phrase did not preserve exact concatenated PCM")
    return path, joined, spans


def token_rows(
    processor: WhisperProcessor,
    model: WhisperForConditionalGeneration,
    samples: np.ndarray,
    retain_attention: bool,
) -> dict[str, Any]:
    normalized = samples.astype(np.float32) / np.float32(32768)
    inputs = processor(
        normalized,
        sampling_rate=SAMPLE_RATE,
        return_tensors="pt",
        return_attention_mask=True,
    )
    feature_mask = inputs["attention_mask"]
    valid_feature_frames = int(feature_mask.sum().item())
    valid_encoder_frames = (valid_feature_frames + 1) // 2
    device_inputs = {name: tensor.to("cuda") for name, tensor in inputs.items()}
    with torch.inference_mode():
        generated = model.generate(
            **device_inputs,
            do_sample=False,
            max_new_tokens=32,
        )
    ids = [int(value) for value in generated[0].tolist()]
    result: dict[str, Any] = {
        "token_ids": ids,
        "token_pieces": [
            processor.tokenizer.decode(
                [token],
                skip_special_tokens=False,
                clean_up_tokenization_spaces=False,
            )
            for token in ids
        ],
        "text": processor.batch_decode(
            generated,
            skip_special_tokens=True,
            clean_up_tokenization_spaces=False,
        )[0],
        "valid_feature_frames": valid_feature_frames,
        "valid_encoder_frames": valid_encoder_frames,
    }
    if not retain_attention:
        return result

    start = torch.full(
        (1, 1),
        int(model.config.decoder_start_token_id),
        dtype=generated.dtype,
        device=generated.device,
    )
    decoder_input = torch.cat((start, generated[:, :-1]), dim=1)
    with torch.inference_mode():
        output = model(
            input_features=device_inputs["input_features"],
            attention_mask=device_inputs["attention_mask"],
            decoder_input_ids=decoder_input,
            output_attentions=True,
            return_dict=True,
        )
    attention = (
        output.cross_attentions[-1][0, :, : len(ids), :valid_encoder_frames]
        .detach()
        .to(device="cpu", dtype=torch.float32)
        .contiguous()
        .numpy()
    )
    raw = attention.view(np.uint32)
    rows = []
    for head in range(raw.shape[0]):
        for token in range(raw.shape[1]):
            rows.append(
                {
                    "token_ordinal": token,
                    "head": head,
                    "words": [int(value) for value in raw[head, token].tolist()],
                }
            )
    result["attention"] = {
        "layer": len(output.cross_attentions) - 1,
        "layers": len(output.cross_attentions),
        "heads": int(raw.shape[0]),
        "tokens": int(raw.shape[1]),
        "frames": int(raw.shape[2]),
        "dtype": "ieee754-binary32-raw-u32",
        "rows": rows,
    }
    return result


def phrase_record(
    specification: dict[str, Any],
    components: dict[str, dict[str, Any]],
    phrase_dir: Path,
    processor: WhisperProcessor,
    model: WhisperForConditionalGeneration,
) -> dict[str, Any]:
    path, samples, spans = concatenate(
        specification["id"], specification["components"], components, phrase_dir
    )
    inherited = token_rows(processor, model, samples, retain_attention=True)
    if inherited["text"] != specification["expected_text"]:
        raise RuntimeError(
            f"{specification['id']} returned {inherited['text']!r}, "
            f"expected {specification['expected_text']!r}"
        )
    frame_map = []
    for frame in range(inherited["valid_encoder_frames"]):
        center = min(frame * BLOCK_SAMPLES + BLOCK_SAMPLES // 2, samples.size - 1)
        span = next(row for row in spans if row["start"] <= center < row["end"])
        frame_map.append(
            {
                "frame": frame,
                "role": span["role"],
                "component": span["component"],
                "component_block": (center - span["start"]) // BLOCK_SAMPLES,
            }
        )
    inherited["attention"]["frame_map"] = frame_map
    return {
        "id": specification["id"],
        "components": spans,
        "path": str(path.resolve()),
        "sha256": sha256(path),
        "samples": int(samples.size),
        "sample_rate": SAMPLE_RATE,
        "inherited": inherited,
    }


def probe_record(
    specification: dict[str, Any],
    components: dict[str, dict[str, Any]],
    phrase_dir: Path,
    processor: WhisperProcessor,
    model: WhisperForConditionalGeneration,
) -> dict[str, Any]:
    ordered = specification["extras"] + specification["core"]
    path, samples, spans = concatenate(
        specification["id"], ordered, components, phrase_dir
    )
    parent = token_rows(processor, model, samples, retain_attention=False)
    return {
        **specification,
        "assembled_components": spans,
        "path": str(path.resolve()),
        "sha256": sha256(path),
        "samples": int(samples.size),
        "sample_rate": SAMPLE_RATE,
        "always_parent_control": parent,
    }


def write_new(path: Path, value: dict[str, Any]) -> None:
    payload = (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def main() -> None:
    arguments = parse_args()
    model_root = arguments.model.resolve()
    output = arguments.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    component_dir = output / "components"
    phrase_dir = output / "phrases"
    component_dir.mkdir()
    phrase_dir.mkdir()

    weights = model_root / "model.safetensors"
    if not weights.is_file():
        raise RuntimeError(f"{weights} is not the fixed Whisper weight file")

    started = time.monotonic_ns()
    torch.cuda.reset_peak_memory_stats()
    processor = WhisperProcessor.from_pretrained(model_root, local_files_only=True)
    model = WhisperForConditionalGeneration.from_pretrained(
        model_root,
        local_files_only=True,
        attn_implementation="eager",
    ).to("cuda")
    model.eval()

    with tempfile.TemporaryDirectory(prefix="eros-audio-source-") as scratch_name:
        scratch = Path(scratch_name)
        components = {
            identifier: synthesize_component(
                identifier, text, voice, component_dir, scratch
            )
            for identifier, (text, voice) in COMPONENTS.items()
        }

    training = [
        phrase_record(row, components, phrase_dir, processor, model) for row in TRAINING
    ]
    probes = [
        probe_record(row, components, phrase_dir, processor, model) for row in PROBES
    ]
    elapsed_micros = (time.monotonic_ns() - started) // 1_000
    source = {
        "schema": SCHEMA,
        "observation_id": "eros-audio-contextual-ecology-01",
        "question": (
            "Can exact acoustic support receive a complete inherited frame-token "
            "return and change later context-local audio conduct?"
        ),
        "fixed_law": {
            "sample_rate": SAMPLE_RATE,
            "sample_format": "mono-signed-pcm16-little-endian",
            "block_samples": BLOCK_SAMPLES,
            "block_duration_ratio_seconds": [BLOCK_SAMPLES, SAMPLE_RATE],
            "retained_attention_cut": (
                "final decoder layer; all heads; all generated token positions; "
                "all unpadded encoder frames"
            ),
            "numerical_law": (
                "PCM and chronology are integers. Retained model activations are exact "
                "IEEE-754 binary32 codewords addressed by tensor coordinates; no decimal "
                "value, top-k edge, threshold, or aggregate is causal."
            ),
        },
        "instrument": {
            "model_path": str(model_root),
            "model_weights_sha256": sha256(weights),
            "model_weights_bytes": weights.stat().st_size,
            "torch": torch.__version__,
            "transformers": __import__("transformers").__version__,
            "torch_cuda": torch.version.cuda,
            "gpu": torch.cuda.get_device_name(0),
            "gpu_peak_allocated_bytes": int(torch.cuda.max_memory_allocated()),
            "espeak": command_text(["espeak-ng", "--version"]).splitlines()[0],
            "ffmpeg": command_text(["ffmpeg", "-version"]).splitlines()[0],
            "source_generation_micros": elapsed_micros,
            "parent_training_consultations": len(training),
            "always_parent_control_consultations": len(probes),
        },
        "components": list(components.values()),
        "training": training,
        "probes": probes,
        "stopping_condition": (
            "Stop after the three context-local probes and the changed-context, "
            "chronology, held-speaker, no-return, and empty-standing foils."
        ),
    }
    write_new(output / "SOURCE.json", source)
    print(output / "SOURCE.json")


if __name__ == "__main__":
    main()
