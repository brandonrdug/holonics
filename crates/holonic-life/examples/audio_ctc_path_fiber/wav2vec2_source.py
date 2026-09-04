#!/usr/bin/env python3
"""Freeze the bounded Speech Commands / Wav2Vec2 CTC field without causal hashes."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
import soundfile as sf
import torch
import transformers
from transformers import Wav2Vec2ForCTC, Wav2Vec2Processor


SCHEMA = "eros.audio-ctc-path-fiber.source.v1"
OBSERVATION_ID = "eros-audio-ctc-path-fiber-01"
SAMPLE_RATE = 16_000

CONTEXTS = [
    {
        "id": 1,
        "name": "turn",
        "atoms": [1],
        "consequence": {"id": 1, "name": "direction"},
    },
    {
        "id": 2,
        "name": "answer",
        "atoms": [2],
        "consequence": {"id": 2, "name": "correctness"},
    },
]
UNTRAINED_CONTEXT = {"id": 3, "name": "copy", "atoms": [3]}


@dataclass(frozen=True)
class Dyadic:
    numerator: int
    denominator_exponent: int

    def __post_init__(self) -> None:
        if self.numerator < 0 or self.denominator_exponent < 0:
            raise ValueError("a source probability dyadic must be nonnegative")

    @staticmethod
    def zero() -> "Dyadic":
        return Dyadic(0, 0)

    @staticmethod
    def one() -> "Dyadic":
        return Dyadic(1, 0)

    def normalized(self) -> "Dyadic":
        numerator = self.numerator
        exponent = self.denominator_exponent
        if numerator == 0:
            return Dyadic.zero()
        while exponent > 0 and numerator & 1 == 0:
            numerator >>= 1
            exponent -= 1
        return Dyadic(numerator, exponent)

    def add(self, other: "Dyadic") -> "Dyadic":
        exponent = max(self.denominator_exponent, other.denominator_exponent)
        numerator = (
            (self.numerator << (exponent - self.denominator_exponent))
            + (other.numerator << (exponent - other.denominator_exponent))
        )
        return Dyadic(numerator, exponent).normalized()

    def multiply(self, other: "Dyadic") -> "Dyadic":
        return Dyadic(
            self.numerator * other.numerator,
            self.denominator_exponent + other.denominator_exponent,
        ).normalized()

    def compare(self, other: "Dyadic") -> int:
        exponent = max(self.denominator_exponent, other.denominator_exponent)
        left = self.numerator << (exponent - self.denominator_exponent)
        right = other.numerator << (exponent - other.denominator_exponent)
        return (left > right) - (left < right)

    def wire(self) -> dict[str, Any]:
        value = self.normalized()
        return {
            "numerator_hex": format(value.numerator, "x"),
            "denominator_exponent": value.denominator_exponent,
        }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True, type=Path)
    parser.add_argument("--speech-commands", required=True, type=Path)
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


def speaker(relative: str) -> str:
    return Path(relative).name.split("_nohash_", 1)[0]


def fixed_occurrences(root: Path) -> list[dict[str, Any]]:
    validation = set((root / "validation_list.txt").read_text().splitlines())
    testing = set((root / "testing_list.txt").read_text().splitlines())
    training: list[str] = []
    training_speakers: set[str] = set()
    for path in sorted((root / "right").glob("*.wav")):
        relative = path.relative_to(root).as_posix()
        source_speaker = speaker(relative)
        if (
            relative not in validation
            and relative not in testing
            and source_speaker not in training_speakers
        ):
            training.append(relative)
            training_speakers.add(source_speaker)
            if len(training) == 2:
                break
    if len(training) != 2:
        raise RuntimeError("the fixed split does not supply two right training speakers")

    held_right = next(
        (
            relative
            for relative in sorted(testing)
            if relative.startswith("right/")
            and speaker(relative) not in training_speakers
        ),
        None,
    )
    if held_right is None:
        raise RuntimeError("the fixed split does not supply one held right speaker")
    used = training_speakers | {speaker(held_right)}
    held_left = next(
        (
            relative
            for relative in sorted(testing)
            if relative.startswith("left/") and speaker(relative) not in used
        ),
        None,
    )
    if held_left is None:
        raise RuntimeError("the fixed split does not supply one held left speaker")

    return [
        {
            "ordinal": 1,
            "role": "cultivation",
            "context_id": CONTEXTS[0]["id"],
            "partition": "training",
            "observer_label": "right",
            "relative_path": training[0],
        },
        {
            "ordinal": 2,
            "role": "cultivation",
            "context_id": CONTEXTS[1]["id"],
            "partition": "training",
            "observer_label": "right",
            "relative_path": training[1],
        },
        {
            "ordinal": 3,
            "role": "held-positive",
            "context_id": None,
            "partition": "testing",
            "observer_label": "right",
            "relative_path": held_right,
        },
        {
            "ordinal": 4,
            "role": "held-foil",
            "context_id": None,
            "partition": "testing",
            "observer_label": "left",
            "relative_path": held_left,
        },
    ]


def decode_binary32(word: int) -> Dyadic:
    sign = word >> 31
    exponent = word >> 23 & 0xFF
    fraction = word & 0x7FFFFF
    if sign:
        raise RuntimeError("the inherited probability field contains a negative word")
    if exponent == 0xFF:
        raise RuntimeError("the inherited probability field contains a nonfinite word")
    if exponent == 0:
        return Dyadic(fraction, 149).normalized()
    significand = (1 << 23) | fraction
    power = exponent - 127 - 23
    if power >= 0:
        return Dyadic(significand << power, 0).normalized()
    return Dyadic(significand, -power).normalized()


def ctc_measure(
    probability_words: list[int],
    frames: int,
    alphabet: int,
    blank: int,
    labels: list[int],
) -> tuple[Dyadic, int]:
    if not labels or frames <= 0 or len(probability_words) != frames * alphabet:
        raise RuntimeError("one CTC fiber has an invalid extent")
    extended: list[int] = [blank]
    for label in labels:
        extended.extend((label, blank))
    previous = [Dyadic.zero() for _ in extended]
    previous[0] = decode_binary32(probability_words[blank])
    previous[1] = decode_binary32(probability_words[labels[0]])
    nonzero_states = int(previous[0].numerator != 0) + int(
        previous[1].numerator != 0
    )
    for frame in range(1, frames):
        current = [Dyadic.zero() for _ in extended]
        base = frame * alphabet
        for state, label in enumerate(extended):
            incoming = previous[state]
            if state >= 1:
                incoming = incoming.add(previous[state - 1])
            if (
                state >= 2
                and label != blank
                and label != extended[state - 2]
            ):
                incoming = incoming.add(previous[state - 2])
            current[state] = decode_binary32(
                probability_words[base + label]
            ).multiply(incoming)
            nonzero_states += int(current[state].numerator != 0)
        previous = current
    measure = previous[-1].add(previous[-2])
    return measure, nonzero_states


def token_ids(
    processor: Wav2Vec2Processor, command: str, blank: int
) -> list[int]:
    encoded = [
        int(value)
        for value in processor.tokenizer(
            command.upper(), add_special_tokens=False
        ).input_ids
    ]
    if not encoded or blank in encoded:
        raise RuntimeError(f"command {command!r} does not have a lawful nonblank CTC path")
    return encoded


def process_occurrence(
    specification: dict[str, Any],
    root: Path,
    processor: Wav2Vec2Processor,
    model: Wav2Vec2ForCTC,
    commands: list[dict[str, Any]],
    blank: int,
) -> dict[str, Any]:
    path = (root / specification["relative_path"]).resolve()
    samples, rate = sf.read(path, dtype="int16")
    if rate != SAMPLE_RATE or samples.ndim != 1 or samples.size == 0:
        raise RuntimeError(f"{path} is not nonempty mono signed PCM16 at 16 kHz")
    normalized = samples.astype(np.float32) / np.float32(32768)
    inputs = processor(
        normalized,
        sampling_rate=SAMPLE_RATE,
        return_tensors="pt",
        return_attention_mask=True,
    )
    input_length = int(inputs["attention_mask"].sum().item())
    expected_frames = int(
        model._get_feat_extract_output_lengths(
            torch.tensor([input_length], dtype=torch.long)
        )[0].item()
    )
    device_inputs = {name: tensor.to("cuda") for name, tensor in inputs.items()}
    with torch.inference_mode():
        logits = model(**device_inputs).logits[0, :expected_frames]
        probabilities = torch.softmax(logits.to(dtype=torch.float32), dim=-1)
    raw = (
        probabilities.detach()
        .to(device="cpu", dtype=torch.float32)
        .contiguous()
        .numpy()
        .view(np.uint32)
    )
    if raw.ndim != 2 or raw.shape[0] != expected_frames:
        raise RuntimeError(f"{path} returned an invalid probability field")
    words = [int(value) for value in raw.reshape(-1).tolist()]
    frame_sums = []
    for frame in range(raw.shape[0]):
        total = Dyadic.zero()
        for value in raw[frame]:
            total = total.add(decode_binary32(int(value)))
        frame_sums.append(total.wire())

    fibers = []
    measured: list[tuple[str, Dyadic]] = []
    for command in commands:
        measure, nonzero_states = ctc_measure(
            words,
            int(raw.shape[0]),
            int(raw.shape[1]),
            blank,
            command["token_ids"],
        )
        measured.append((command["text"], measure))
        fibers.append(
            {
                "command_id": command["id"],
                "text": command["text"],
                "measure": measure.wire(),
                "nonzero_forward_states": nonzero_states,
            }
        )
    order = sorted(
        measured,
        key=lambda row: CtcOrderKey(row[1], row[0]),
    )
    winner = order[0][0]
    tied = [
        command
        for command, measure in order
        if measure.compare(order[0][1]) == 0
    ]
    greedy_ids = raw.argmax(axis=1).tolist()
    greedy_text = processor.decode(greedy_ids)
    return {
        **specification,
        "speaker": speaker(specification["relative_path"]),
        "path": str(path),
        "sha256": sha256(path),
        "sample_rate": rate,
        "samples": int(samples.size),
        "pcm_min": int(samples.min()),
        "pcm_max": int(samples.max()),
        "field": {
            "frames": int(raw.shape[0]),
            "alphabet": int(raw.shape[1]),
            "dtype": "ieee754-binary32-raw-u32-exact-dyadic",
            "probability_words": words,
            "frame_sums": frame_sums,
        },
        "fibers": fibers,
        "fiber_order": [command for command, _ in order],
        "unique_winner": len(tied) == 1,
        "derived_expression": winner if len(tied) == 1 else None,
        "observer_greedy_text": greedy_text,
        "observer_greedy_ids": [int(value) for value in greedy_ids],
    }


class CtcOrderKey:
    """Sort exact dyadics descending, then command text ascending."""

    __slots__ = ("measure", "text")

    def __init__(self, measure: Dyadic, text: str) -> None:
        self.measure = measure
        self.text = text

    def __lt__(self, other: "CtcOrderKey") -> bool:
        comparison = self.measure.compare(other.measure)
        return comparison > 0 if comparison else self.text < other.text


def main() -> None:
    arguments = parse_args()
    model_root = arguments.model.resolve()
    speech_root = arguments.speech_commands.resolve()
    output = arguments.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    weights = model_root / "model.safetensors"
    if not weights.is_file():
        raise RuntimeError(f"{weights} is not the fixed Wav2Vec2 weight file")
    if not (speech_root / "testing_list.txt").is_file():
        raise RuntimeError(f"{speech_root} is not the fixed Speech Commands root")

    started = time.monotonic_ns()
    torch.cuda.reset_peak_memory_stats()
    processor = Wav2Vec2Processor.from_pretrained(
        model_root, local_files_only=True
    )
    model = Wav2Vec2ForCTC.from_pretrained(
        model_root, local_files_only=True
    ).to("cuda")
    model.eval()
    blank = int(model.config.pad_token_id)
    vocabulary = sorted(
        (
            {"token": token, "id": int(identifier)}
            for token, identifier in processor.tokenizer.get_vocab().items()
        ),
        key=lambda row: row["id"],
    )
    command_names = sorted(
        path.name
        for path in speech_root.iterdir()
        if path.is_dir() and path.name != "_background_noise_"
    )
    commands = [
        {
            "id": ordinal + 1,
            "text": command,
            "token_ids": token_ids(processor, command, blank),
        }
        for ordinal, command in enumerate(command_names)
    ]
    if len(commands) != 35:
        raise RuntimeError(f"the command population changed to {len(commands)}")

    occurrence_specs = fixed_occurrences(speech_root)
    occurrences = [
        process_occurrence(
            specification,
            speech_root,
            processor,
            model,
            commands,
            blank,
        )
        for specification in occurrence_specs
    ]
    for occurrence in occurrences:
        if (
            not occurrence["unique_winner"]
            or occurrence["derived_expression"]
            != occurrence["observer_label"]
        ):
            raise RuntimeError(
                f"fixed occurrence {occurrence['relative_path']} derives "
                f"{occurrence['derived_expression']!r}, expected "
                f"{occurrence['observer_label']!r}"
            )
    elapsed_micros = (time.monotonic_ns() - started) // 1_000
    source = {
        "schema": SCHEMA,
        "observation_id": OBSERVATION_ID,
        "question": (
            "Can nonidentical pronunciations found and later recruit one expression "
            "through complete exact-dyadic CTC path fibers without causal digests?"
        ),
        "selection_law": (
            "first two distinct-speaker training right recordings; first unseen-speaker "
            "testing right; first fourth-speaker testing left; all lexicographic"
        ),
        "numerical_law": (
            "The inherited model emits finite binary32 probability codewords. Each word "
            "is decoded as an exact dyadic; every 35-command CTC forward recurrence uses "
            "only integer addition, multiplication, normalization, and comparison."
        ),
        "instrument": {
            "model_path": str(model_root),
            "model_weights_sha256": sha256(weights),
            "model_weights_bytes": weights.stat().st_size,
            "dataset_root": str(speech_root),
            "dataset_archive_sha256": sha256(
                speech_root.parent / "speech_commands_v0.02.tar.gz"
            ),
            "torch": torch.__version__,
            "transformers": transformers.__version__,
            "numpy": np.__version__,
            "soundfile": sf.__version__,
            "torch_cuda": torch.version.cuda,
            "gpu": torch.cuda.get_device_name(0),
            "gpu_peak_allocated_bytes": int(torch.cuda.max_memory_allocated()),
            "source_generation_micros": elapsed_micros,
            "nvidia_smi": command_text(
                [
                    "nvidia-smi",
                    "--query-gpu=name,driver_version,memory.total",
                    "--format=csv,noheader",
                ]
            ),
        },
        "sample_rate": SAMPLE_RATE,
        "blank_token_id": blank,
        "vocabulary": vocabulary,
        "commands": commands,
        "contexts": CONTEXTS,
        "untrained_context": UNTRAINED_CONTEXT,
        "occurrences": occurrences,
        "causal_digest_policy": (
            "All SHA-256 values are provenance only. No causal interface, branch, "
            "expression, context, or occurrence capability is derived from a digest."
        ),
        "stopping_condition": (
            "Stop after two cultivation returns, held-right context forks, held-left "
            "foils, the untrained-context foil, empty Standing, and exact rest/remount."
        ),
    }
    write_new(output / "SOURCE.json", source)
    print(output / "SOURCE.json")


if __name__ == "__main__":
    main()
