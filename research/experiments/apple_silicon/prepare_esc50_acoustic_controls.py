#!/usr/bin/env python3
"""Prepare exact, non-semantic ESC-50 acoustic controls for the AS4 experiment.

The source WAVs remain untouched. A fixed-size window is selected by an amplitude-only observer
from each selected source, then three replayable receiver controls are emitted: original order,
chronology reversal, and exact polarity inversion. No class/category field enters the control
manifest, and no HNA/native-current operation is invoked.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import soundfile as sf


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def pcm_identity(samples: np.ndarray) -> str:
    return sha256_bytes(np.asarray(samples, dtype=np.int16).tobytes())


def pcm_metrics(samples: np.ndarray) -> dict[str, int | float]:
    values = np.asarray(samples, dtype=np.int64)
    return {
        "frames": int(values.size),
        "peak_abs": int(np.max(np.abs(values))) if values.size else 0,
        "signed_sum": int(np.sum(values, dtype=np.int64)),
        "alternating_sum": int(np.sum(values * np.where(np.arange(values.size) % 2 == 0, 1, -1), dtype=np.int64)),
        "square_sum": int(np.sum(values * values, dtype=np.int64)),
        "pcm16_sha256": pcm_identity(values),
    }


def write_pcm16(path: Path, samples: np.ndarray, sample_rate: int) -> None:
    sf.write(path, np.asarray(samples, dtype=np.int16), sample_rate, format="WAV", subtype="PCM_16")
    readback, rate = sf.read(path, dtype="int16", always_2d=True)
    if rate != sample_rate or readback.shape[1] != 1 or not np.array_equal(readback[:, 0], samples):
        raise RuntimeError(f"PCM16 WAV did not round-trip exactly: {path}")


def choose_window(samples: np.ndarray, sample_rate: int, window_seconds: float, threshold: float) -> tuple[int, int, str, float]:
    length = int(round(sample_rate * window_seconds))
    if length <= 0 or length > samples.size:
        raise ValueError("window extent is outside the source")
    hop = max(1, length // 4)
    best: tuple[float, int] | None = None
    for begin in range(0, samples.size - length + 1, hop):
        window = samples[begin : begin + length]
        rms = float(np.sqrt(np.mean(np.square(window.astype(np.float64) / 32768.0))))
        if best is None or rms > best[0]:
            best = (rms, begin)
    assert best is not None
    rms, begin = best
    basis = "maximum-window-rms" if rms >= threshold else "maximum-window-rms-below-threshold"
    return begin, begin + length, basis, rms


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(".local/datasets/esc50"))
    parser.add_argument("--output", type=Path, default=Path(".local/datasets/esc50-as4-controls"))
    parser.add_argument("--count", type=int, default=10)
    parser.add_argument("--window-seconds", type=float, default=0.25, help="initial control duration")
    parser.add_argument("--base-window-seconds", type=float, default=1.0, help="meaningful source base duration")
    parser.add_argument("--amplitude-threshold", type=float, default=0.01)
    args = parser.parse_args()
    if not 1 <= args.count <= 2_000:
        parser.error("--count must be between 1 and 2000")
    if not math.isfinite(args.window_seconds) or not args.window_seconds > 0 or not args.window_seconds < 5:
        parser.error("--window-seconds must be finite and in (0, 5)")
    if (
        not math.isfinite(args.base_window_seconds)
        or not args.base_window_seconds >= args.window_seconds
        or not args.base_window_seconds < 5
    ):
        parser.error("--base-window-seconds must be finite, at least --window-seconds, and below 5")
    if not math.isfinite(args.amplitude_threshold) or not 0 <= args.amplitude_threshold < 1:
        parser.error("--amplitude-threshold must be in [0, 1)")

    metadata = list(csv.DictReader((args.source / "meta/esc50.csv").open(newline="", encoding="utf-8")))
    by_fold: dict[str, list[dict[str, str]]] = {}
    for row in sorted(metadata, key=lambda item: item["filename"]):
        by_fold.setdefault(row["fold"], []).append(row)
    ordered = []
    folds = sorted(by_fold)
    while len(ordered) < len(metadata):
        for fold in folds:
            if by_fold[fold]:
                ordered.append(by_fold[fold].pop(0))
    selected = ordered[: args.count]
    candidate_index = args.count

    control_dir = args.output / "controls"
    control_dir.mkdir(parents=True, exist_ok=True)
    records = []
    polarity_refusals = []
    for row in selected:
        source_path = args.source / "audio" / row["filename"]
        source_bytes = source_path.read_bytes()
        source_samples, sample_rate = sf.read(source_path, dtype="int16", always_2d=True)
        if sample_rate != 44_100 or source_samples.shape[1] != 1:
            raise ValueError(f"source is not the admitted ESC-50 mono 44.1 kHz WAV: {source_path}")
        samples = source_samples[:, 0]
        base_begin, base_end, selection_basis, observed_rms = choose_window(
            samples, sample_rate, args.base_window_seconds, args.amplitude_threshold
        )
        control_length = int(round(sample_rate * args.window_seconds))
        base_center = (base_begin + base_end) // 2
        begin = max(base_begin, base_center - control_length // 2)
        end = begin + control_length
        if end > base_end:
            end = base_end
            begin = end - control_length
        base_window = samples[base_begin:base_end].copy()
        window = samples[begin:end].copy()
        inverted = -window.astype(np.int32)
        if np.any(inverted < -32768) or np.any(inverted > 32767):
            polarity_refusals.append(
                {
                    "source_filename": row["filename"],
                    "source_sha256": sha256_bytes(source_bytes),
                    "reason": "exact polarity inversion is outside signed PCM16 domain",
                }
            )
            if candidate_index >= len(ordered):
                raise ValueError("not enough ESC-50 sources admit exact PCM16 polarity controls")
            selected.append(ordered[candidate_index])
            candidate_index += 1
            continue
        variants = {
            "base-original": base_window,
            "original": window,
            "reversed": window[::-1].copy(),
            "polarity-inverted": inverted.astype(np.int16),
        }
        variant_records = []
        for name, control in variants.items():
            output_name = f"{Path(row['filename']).stem}__{name}.wav"
            output_path = control_dir / output_name
            write_pcm16(output_path, control, sample_rate)
            variant_records.append(
                {
                    "variant": name,
                    "path": str(output_path.relative_to(args.output)),
                    "pcm_metrics": pcm_metrics(control),
                }
            )
        records.append(
            {
                "source_filename": row["filename"],
                "source_fold": int(row["fold"]),
                "source_sha256": sha256_bytes(source_bytes),
                "source_sample_rate": sample_rate,
                "source_frames": int(samples.size),
                "window_sample_from": begin,
                "window_sample_to": end,
                "base_window_sample_from": base_begin,
                "base_window_sample_to": base_end,
                "base_window_seconds": args.base_window_seconds,
                "window_seconds": args.window_seconds,
                "selection_basis": selection_basis,
                "observed_window_rms": observed_rms,
                "amplitude_threshold": args.amplitude_threshold,
                "variants": variant_records,
                "native_current_metrics": None,
                "native_current_status": "not-run; pending AS4 native attachment",
            }
        )

    manifest = args.output / "listening_manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "schema": "holonics.as4.acoustic-control-manifest.v1",
                "source": "ESC-50 original WAVs",
                "source_root": str(args.source),
                "selection": "deterministic round-robin over source folds; amplitude-only window observer",
                "labels_entered_control_manifest": False,
                "sample_rate_preserved": True,
                "resampling_applied": False,
                "native_learner_invoked": False,
                "gpu_experiment_invoked": False,
                "polarity_refusals": polarity_refusals,
                "controls": records,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"output": str(args.output), "source_count": len(records), "control_count": len(records) * 4}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
