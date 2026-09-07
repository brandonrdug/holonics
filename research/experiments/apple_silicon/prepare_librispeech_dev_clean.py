#!/usr/bin/env python3
"""Fetch a bounded LibriSpeech dev-clean companion and make exact PCM16 WAV faces.

This script only admits source audio and metadata. It does not invoke a model, ASR/TTS,
segmentation policy, or native HNA owner. The transcript remains provenance metadata beside the
source speaker/chapter identifiers; callers decide separately whether and how an occurrence is
presented to a native ingress.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import sys
from pathlib import Path

import soundfile as sf
from datasets import Audio, load_dataset
from huggingface_hub import HfApi

DATASET = "openslr/librispeech_asr"
CONFIG = "clean"
SPLIT = "validation"  # LibriSpeech dev-clean on the official source page.
LICENSE = "CC BY 4.0"
OPENSLR_URL = "https://www.openslr.org/12"
HF_URL = "https://huggingface.co/datasets/openslr/librispeech_asr"


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def convert_flac_to_wav(flac_bytes: bytes) -> tuple[bytes, int, int, int, str]:
    with sf.SoundFile(io.BytesIO(flac_bytes), mode="r") as source:
        if source.samplerate != 16_000 or source.channels != 1 or source.subtype != "PCM_16":
            raise ValueError(
                f"source is not admitted LibriSpeech mono PCM16/16kHz: "
                f"rate={source.samplerate} channels={source.channels} subtype={source.subtype}"
            )
        samples = source.read(dtype="int16", always_2d=True)
        frames = len(samples)
        pcm_identity = sha256(samples.tobytes())
    output = io.BytesIO()
    with sf.SoundFile(
        output,
        mode="w",
        samplerate=16_000,
        channels=1,
        subtype="PCM_16",
        format="WAV",
    ) as target:
        target.write(samples)
    wav_bytes = output.getvalue()
    with sf.SoundFile(io.BytesIO(wav_bytes), mode="r") as check:
        if check.samplerate != 16_000 or check.channels != 1 or check.subtype != "PCM_16":
            raise ValueError("generated WAV did not retain mono PCM16/16kHz format")
        roundtrip = check.read(dtype="int16", always_2d=True)
    if sha256(roundtrip.tobytes()) != pcm_identity:
        raise ValueError("FLAC-to-WAV PCM sample identity changed during conversion")
    return wav_bytes, 16_000, 1, frames, pcm_identity


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(".local/datasets/librispeech-dev-clean-subset"))
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--revision", default="main", help="HF revision; resolved SHA is recorded")
    args = parser.parse_args()
    if not 1 <= args.count <= 2_703:
        parser.error("--count must be between 1 and the 2703-row clean validation split")

    info = HfApi().dataset_info(DATASET, revision=args.revision)
    revision = info.sha
    root = args.output
    flac_dir = root / "flac"
    wav_dir = root / "wav"
    flac_dir.mkdir(parents=True, exist_ok=True)
    wav_dir.mkdir(parents=True, exist_ok=True)

    # Streaming avoids materializing the 342 MB validation parquet. Audio bytes are retained
    # exactly from the mirror before soundfile performs a reversible PCM16 decode/re-encode.
    stream = load_dataset(DATASET, CONFIG, split=SPLIT, revision=revision, streaming=True)
    stream = stream.cast_column("audio", Audio(decode=False))
    rows = []
    total_flac = 0
    total_wav = 0
    for row in stream:
        audio = row["audio"]
        flac_bytes = audio.get("bytes") if isinstance(audio, dict) else None
        if not isinstance(flac_bytes, bytes):
            raise RuntimeError(f"row {row.get('id')} did not return source FLAC bytes")
        identifier = str(row["id"])
        wav_bytes, sample_rate, channels, frames, pcm_identity = convert_flac_to_wav(flac_bytes)
        flac_path = flac_dir / f"{identifier}.flac"
        wav_path = wav_dir / f"{identifier}.wav"
        flac_path.write_bytes(flac_bytes)
        wav_path.write_bytes(wav_bytes)
        rows.append(
            {
                "id": identifier,
                "split": SPLIT,
                "source_flac": str(flac_path.relative_to(root)),
                "source_flac_sha256": sha256(flac_bytes),
                "wav_pcm16": str(wav_path.relative_to(root)),
                "wav_sha256": sha256(wav_bytes),
                "sample_rate": sample_rate,
                "channels": channels,
                "frames": frames,
                "pcm16_sha256": pcm_identity,
                "speaker_id": int(row["speaker_id"]),
                "chapter_id": int(row["chapter_id"]),
                "transcript": str(row["text"]),
            }
        )
        total_flac += len(flac_bytes)
        total_wav += len(wav_bytes)
        if len(rows) >= args.count:
            break
    if len(rows) != args.count:
        raise RuntimeError(f"stream ended after {len(rows)} rows; requested {args.count}")

    manifest = root / "manifest.jsonl"
    with manifest.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    write_json(
        root / "provenance.json",
        {
            "schema": "holonics.speech-companion.provenance.v1",
            "dataset": DATASET,
            "config": CONFIG,
            "split": SPLIT,
            "scope": "first deterministic rows from clean validation/dev-clean",
            "count": len(rows),
            "speaker_ids": sorted({row["speaker_id"] for row in rows}),
            "chapter_ids": sorted({row["chapter_id"] for row in rows}),
            "source_revision": revision,
            "source_revision_requested": args.revision,
            "source_huggingface": HF_URL,
            "source_openslr": OPENSLR_URL,
            "license": LICENSE,
            "format": "source FLAC retained; decoded mono signed PCM16 at 16000 Hz written as WAV",
            "source_flac_bytes": total_flac,
            "wav_bytes": total_wav,
            "transcripts_retained_as_metadata": True,
            "models_or_pretrained_weights_used": False,
            "native_learner_invoked": False,
            "citation": "Panayotov, Chen, Povey, Khudanpur, LibriSpeech: An ASR Corpus Based On Public Domain Audio Books, ICASSP 2015.",
        },
    )
    print(json.dumps({"output": str(root), "count": len(rows), "revision": revision, "flac_bytes": total_flac, "wav_bytes": total_wav}, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
