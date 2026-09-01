#!/usr/bin/env python3
"""Authenticated Gemma-4 vision/audio organ conduct for E2.

The script is an exterior foreign-apparatus mouth.  It reads raw RGB/PCM occurrences, mounts only
one authenticated inherited organ at a time, keeps every tower operation on CUDA, and returns the
foreign BF16 section plus frontier and apparatus testimony.  It does not found the native join;
the Rust E2 driver does that from the returned occurrences through nominal BoundaryId incidence.
"""

from __future__ import annotations

import argparse
import gc
import hashlib
import importlib.util
import json
import time
import wave
from pathlib import Path

import numpy as np
import torch
from PIL import Image
from safetensors import safe_open
from torch.profiler import ProfilerActivity, profile
from transformers import (
    AutoModelForMultimodalLM,
    AutoTokenizer,
    Gemma4AudioFeatureExtractor,
    Gemma4AudioModel,
    Gemma4Config,
    Gemma4VisionModel,
)


VISION_PREFIX = "model.vision_tower."
AUDIO_PREFIX = "model.audio_tower."
VISION_PROJECTION = "model.embed_vision.embedding_projection.weight"
AUDIO_PROJECTION = "model.embed_audio.embedding_projection.weight"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def module_source(module: str) -> dict[str, str]:
    """Return the installed source path and identity without importing optional apparatus."""
    specification = importlib.util.find_spec(module)
    if specification is None or specification.origin is None:
        raise RuntimeError(f"cannot bind installed source for {module}")
    path = Path(specification.origin)
    return {"path": path.as_posix(), "sha256": file_sha(path)}


def bf16_bytes(value: torch.Tensor) -> bytes:
    return value.detach().contiguous().view(torch.uint16).cpu().numpy().astype("<u2", copy=False).tobytes()


def load_prefixed(model: torch.nn.Module, container: safe_open, prefix: str) -> int:
    state = {name[len(prefix) :]: container.get_tensor(name) for name in container.keys() if name.startswith(prefix)}
    incompatibility = model.load_state_dict(state)
    if incompatibility.missing_keys or incompatibility.unexpected_keys:
        raise RuntimeError(f"{prefix} did not bind completely: {incompatibility}")
    return len(state)


def project_without_gain(hidden: torch.Tensor, weight: torch.Tensor, eps: float) -> torch.Tensor:
    normalized = hidden.float() * torch.pow(hidden.float().pow(2).mean(-1, keepdim=True) + eps, -0.5)
    return torch.nn.functional.linear(normalized.to(hidden.dtype), weight)


def profiler_events(session: profile) -> int:
    return sum(1 for event in session.events() if str(event.device_type).endswith("CUDA"))


def conduct_vision_section(
    model: Gemma4VisionModel,
    projection: torch.Tensor,
    pixels: np.ndarray,
    output: Path,
    prefix: str,
    config: Gemma4Config,
) -> dict:
    if pixels.shape != (144, 144, 3):
        raise RuntimeError(f"{prefix} is not one exact 144x144 RGB occurrence")
    raw_pixels = torch.from_numpy(pixels.copy()).to(device="cuda")
    channels = raw_pixels.permute(2, 0, 1)
    patches = (
        channels.reshape(3, 9, 16, 9, 16)
        .permute(1, 3, 2, 4, 0)
        .reshape(1, 81, 768)
        .to(torch.bfloat16)
        / 255
    )
    positions = torch.stack(
        torch.meshgrid(
            torch.arange(9, device="cuda"),
            torch.arange(9, device="cuda"),
            indexing="xy",
        ),
        dim=-1,
    ).reshape(1, 81, 2)
    layers: list[torch.Tensor] = []
    hooks = [
        layer.register_forward_hook(
            lambda _m, _i, value, sink=layers: sink.append(value)
        )
        for layer in model.encoder.layers
    ]
    with torch.inference_mode(), profile(
        activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA]
    ) as prof:
        tower = model(pixel_values=patches, pixel_position_ids=positions).last_hidden_state
        projected = project_without_gain(
            tower, projection, config.vision_config.rms_norm_eps
        )
    for hook in hooks:
        hook.remove()
    torch.cuda.synchronize()
    entering = bf16_bytes(layers[0])
    entering_name = f"{prefix}-entering.bf16"
    (output / entering_name).write_bytes(entering)
    final = bf16_bytes(projected)
    final_name = f"{prefix}-text-space.bf16"
    (output / final_name).write_bytes(final)
    return {
        "patch_shape": [81, 768],
        "tower_shape": list(tower.shape),
        "text_space_shape": list(projected.shape),
        "layer_frontier_sha256": [sha(bf16_bytes(value)) for value in layers],
        "complete_layer_count": len(layers),
        "entering_bf16": entering_name,
        "entering_sha256": sha(entering),
        "returned_bf16": final_name,
        "returned_sha256": sha(final),
        "cuda_kernel_events": profiler_events(prof),
    }


def run_vision(
    root: Path,
    image_path: Path,
    video_frames: list[Path],
    output: Path,
    config: Gemma4Config,
    container: safe_open,
) -> tuple[dict, dict]:
    model = Gemma4VisionModel(config.vision_config)
    tensor_count = load_prefixed(model, container, VISION_PREFIX)
    projection = container.get_tensor(VISION_PROJECTION).to(device="cuda", dtype=torch.bfloat16)
    model.to(device="cuda", dtype=torch.bfloat16).eval()

    raw = np.asarray(Image.open(image_path).convert("RGB"), dtype=np.uint8)
    # Four exact 144x144 restrictions across the first complete equation band. No interpolation,
    # resize, OCR or transcript enters; the complement remains the crop reconstruction fibre.
    crops = [(240, 224), (384, 224), (528, 224), (672, 224)]
    returns = []
    torch.cuda.reset_peak_memory_stats()
    began = time.perf_counter_ns()
    for occurrence_at, (left, top) in enumerate(crops):
        crop = raw[top : top + 144, left : left + 144]
        section = conduct_vision_section(
            model, projection, crop, output, f"vision-{occurrence_at}", config
        )
        crop_bytes = crop.tobytes()
        returns.append(
            {
                "family": occurrence_at // 2,
                "state": occurrence_at % 2,
                "occurrence": f"{image_path}#restriction({left},{top},144,144)",
                "source_sha256": sha(crop_bytes),
                "source_incidence_sha256": sha(
                    image_path.as_posix().encode()
                    + left.to_bytes(4, "little")
                    + top.to_bytes(4, "little")
                    + crop_bytes
                ),
                "crop": [left, top, 144, 144],
                **section,
            }
        )
    frame_returns = []
    for frame_ordinal, frame_path in enumerate(video_frames):
        pixels = np.asarray(Image.open(frame_path).convert("RGB"), dtype=np.uint8)
        section = conduct_vision_section(
            model, projection, pixels, output, f"video-{frame_ordinal}", config
        )
        pixel_bytes = pixels.tobytes()
        frame_returns.append(
            {
                "family": 0,
                "state": frame_ordinal,
                "frame_ordinal": frame_ordinal,
                "occurrence": f"{frame_path}#frame({frame_ordinal})",
                "source_sha256": sha(pixel_bytes),
                "source_incidence_sha256": sha(
                    frame_ordinal.to_bytes(4, "little") + pixel_bytes
                ),
                **section,
            }
        )
    elapsed = time.perf_counter_ns() - began
    vision_receipt = {
        "organ": "inherited-organ-at-nominal-boundary",
        "source_lineage": "Gemma4VisionModel",
        "tensor_count": tensor_count,
        "complete_layer_count": len(model.encoder.layers),
        "resident_weight_parameters": sum(parameter.numel() for parameter in model.parameters()) + projection.numel(),
        "peak_cuda_allocated_octets": torch.cuda.max_memory_allocated(),
        "elapsed_nanoseconds": elapsed,
        "returns": returns,
    }
    video_receipt = {
        "organ": "temporally-ordered-video-through-inherited-vision-organ",
        "source_lineage": "Gemma4VisionModel",
        "tensor_count": tensor_count,
        "complete_layer_count": len(model.encoder.layers),
        "temporal_frame_lineage": True,
        "sampled_frame_count": len(frame_returns),
        "processor_frame_aperture": 32,
        "returns": frame_returns,
        "frame_returns": frame_returns,
    }
    del model, projection
    gc.collect()
    torch.cuda.empty_cache()
    return vision_receipt, video_receipt


def raw_pcm(path: Path) -> tuple[np.ndarray, int]:
    with wave.open(str(path), "rb") as source:
        if source.getnchannels() != 1 or source.getsampwidth() != 2:
            raise RuntimeError(f"{path} is not mono signed 16-bit PCM")
        rate = source.getframerate()
        samples = np.frombuffer(source.readframes(source.getnframes()), dtype="<i2").copy()
    if rate != 16_000:
        raise RuntimeError(f"{path} is {rate} Hz, not the inherited 16 kHz boundary")
    return samples, rate


def gpu_log_mel(samples: np.ndarray, extractor: Gemma4AudioFeatureExtractor) -> torch.Tensor:
    waveform = torch.from_numpy(samples).to(device="cuda", dtype=torch.float32) / 32768
    waveform = torch.nn.functional.pad(waveform, (extractor.frame_length // 2, 0))
    frames = waveform.unfold(0, extractor.frame_length + 1, extractor.hop_length)[..., :-1]
    window = torch.from_numpy(extractor.window).to(device="cuda", dtype=torch.float32)
    spectrum = torch.fft.rfft(frames * window, n=extractor.fft_length, dim=-1).abs()
    mel = torch.from_numpy(extractor.mel_filters.astype(np.float32)).to(device="cuda")
    return torch.log(spectrum @ mel + float(extractor.mel_floor))


def run_audio(root: Path, audio_paths: list[Path], output: Path, config: Gemma4Config, container: safe_open) -> dict:
    model = Gemma4AudioModel(config.audio_config)
    tensor_count = load_prefixed(model, container, AUDIO_PREFIX)
    projection = container.get_tensor(AUDIO_PROJECTION).to(device="cuda", dtype=torch.bfloat16)
    model.to(device="cuda", dtype=torch.bfloat16).eval()
    extractor = Gemma4AudioFeatureExtractor.from_pretrained(root)
    returns = []
    torch.cuda.reset_peak_memory_stats()
    began = time.perf_counter_ns()
    for occurrence_at, path in enumerate(audio_paths):
        samples, rate = raw_pcm(path)
        features = gpu_log_mel(samples, extractor)
        mask = torch.ones((1, features.shape[0]), device="cuda", dtype=torch.bool)
        layers: list[torch.Tensor] = []
        hooks = [layer.register_forward_hook(lambda _m, _i, value, sink=layers: sink.append(value)) for layer in model.layers]
        with torch.inference_mode(), profile(activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA]) as prof:
            tower = model(input_features=features.unsqueeze(0), attention_mask=mask).last_hidden_state
            projected = project_without_gain(tower, projection, config.audio_config.rms_norm_eps)
        for hook in hooks:
            hook.remove()
        torch.cuda.synchronize()
        layer_hashes = [sha(bf16_bytes(value)) for value in layers]
        entering = bf16_bytes(layers[0])
        entering_name = f"audio-{occurrence_at}-entering.bf16"
        (output / entering_name).write_bytes(entering)
        final = bf16_bytes(projected)
        final_name = f"audio-{occurrence_at}-text-space.bf16"
        (output / final_name).write_bytes(final)
        pcm_bytes = samples.astype("<i2", copy=False).tobytes()
        returns.append(
            {
                "family": occurrence_at // 2,
                "state": occurrence_at % 2,
                "occurrence": path.as_posix(),
                "source_sha256": file_sha(path),
                "source_incidence_sha256": sha(rate.to_bytes(4, "little") + pcm_bytes),
                "sample_rate": rate,
                "sample_count": len(samples),
                "feature_shape": list(features.shape),
                "tower_shape": list(tower.shape),
                "text_space_shape": list(projected.shape),
                "layer_frontier_sha256": layer_hashes,
                "complete_layer_count": len(layer_hashes),
                "entering_bf16": entering_name,
                "entering_sha256": sha(entering),
                "returned_bf16": final_name,
                "returned_sha256": sha(final),
                "cuda_kernel_events": profiler_events(prof),
            }
        )
    elapsed = time.perf_counter_ns() - began
    receipt = {
        "organ": "inherited-organ-at-nominal-boundary",
        "source_lineage": "Gemma4AudioModel",
        "tensor_count": tensor_count,
        "complete_layer_count": len(model.layers),
        "resident_weight_parameters": sum(parameter.numel() for parameter in model.parameters()) + projection.numel(),
        "peak_cuda_allocated_octets": torch.cuda.max_memory_allocated(),
        "elapsed_nanoseconds": elapsed,
        "raw_pcm_to_feature_transport": [
            "semicausal zero incidence",
            "320-sample periodic-Hann fronts at 160-sample chronology",
            "512-point resident RFFT magnitude",
            "128-bin HTK mel transport",
            "log passage with source-founded mel floor",
        ],
        "returns": returns,
    }
    del model, projection
    gc.collect()
    torch.cuda.empty_cache()
    return receipt


def run_text(root: Path, proposition: str, output: Path, container: safe_open) -> dict:
    """Run two intervention-separated text occurrences through all 42 decoder layers on CPU.

    E4B's per-layer embedding table cannot coexist with the full body on the 16 GiB card. CPU
    placement is exterior apparatus testimony; the same BF16 weights and model law are used, KV
    caching is disabled, and every layer frontier is returned.
    """
    prompts = [proposition, f"{proposition} Returned under a second exterior occurrence."]
    model = AutoModelForMultimodalLM.from_pretrained(
        root,
        dtype=torch.bfloat16,
        device_map={"": "cpu"},
        low_cpu_mem_usage=True,
    ).eval()
    tokenizer = AutoTokenizer.from_pretrained(root)
    encoded = tokenizer(prompts, return_tensors="pt", padding=True, add_special_tokens=True)
    per_layer: list[list[torch.Tensor]] = [[] for _ in prompts]
    hooks = []

    def retain_frontier(_module, _inputs, value) -> None:
        section = value[0] if isinstance(value, tuple) else value
        for at in range(len(prompts)):
            per_layer[at].append(section[at].detach())

    for layer in model.model.language_model.layers:
        hooks.append(layer.register_forward_hook(retain_frontier))
    began = time.perf_counter_ns()
    with torch.inference_mode():
        returned = model(
            input_ids=encoded["input_ids"],
            attention_mask=encoded["attention_mask"],
            use_cache=False,
            return_dict=True,
        )
    elapsed = time.perf_counter_ns() - began
    for hook in hooks:
        hook.remove()
    returns = []
    for at, prompt in enumerate(prompts):
        last = int(encoded["attention_mask"][at].sum()) - 1
        logits = returned.logits[at, last]
        entering = bf16_bytes(per_layer[at][0])
        entering_name = f"text-{at}-entering.bf16"
        (output / entering_name).write_bytes(entering)
        final = bf16_bytes(logits)
        final_name = f"text-{at}-logits.bf16"
        (output / final_name).write_bytes(final)
        returns.append(
            {
                "family": 0,
                "state": at,
                "occurrence": f"text-occurrence/{at}",
                "source_sha256": sha(prompt.encode()),
                "source_incidence_sha256": sha(at.to_bytes(4, "little") + prompt.encode()),
                "input_token_count": int(encoded["attention_mask"][at].sum()),
                "layer_frontier_sha256": [sha(bf16_bytes(value)) for value in per_layer[at]],
                "complete_layer_count": len(per_layer[at]),
                "entering_bf16": entering_name,
                "entering_sha256": sha(entering),
                "returned_bf16": final_name,
                "returned_sha256": sha(final),
                "text_space_shape": list(logits.shape),
                "top5": torch.topk(logits.float(), 5).indices.tolist(),
                "kv_cache_used": False,
            }
        )
    receipt = {
        "organ": "inherited-organ-at-nominal-boundary",
        "source_lineage": "Gemma4ForConditionalGeneration.language_model",
        "tensor_count": sum(1 for name in container.keys() if name.startswith("model.language_model.")),
        "complete_layer_count": len(model.model.language_model.layers),
        "resident_weight_parameters": sum(parameter.numel() for parameter in model.parameters()),
        "peak_cuda_allocated_octets": 0,
        "elapsed_nanoseconds": elapsed,
        "apparatus": "cpu-bfloat16-complete-tower",
        "returns": returns,
    }
    del model
    gc.collect()
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--proposition", required=True)
    parser.add_argument("--image", type=Path, required=True)
    parser.add_argument("--video-frame", type=Path, nargs=4, required=True)
    parser.add_argument("--audio", type=Path, nargs=4, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    if not torch.cuda.is_available():
        raise RuntimeError("E2 complete inherited conduct requires CUDA")
    torch.manual_seed(0)
    torch.set_grad_enabled(False)
    config = Gemma4Config.from_pretrained(args.model)
    container = safe_open(args.model / "model.safetensors", framework="pt", device="cpu")
    vision, video = run_vision(
        args.model, args.image, args.video_frame, args.output, config, container
    )
    audio = run_audio(args.model, args.audio, args.output, config, container)
    text = run_text(args.model, args.proposition, args.output, container)
    receipt = {
        "schema": "holonics.scf2.complete-gemma4-excitation.v2",
        "truth_status": "implemented-exact-source-binding; measured-foreign-bfloat16-conduct",
        "model": {
            "container": (args.model / "model.safetensors").as_posix(),
            "container_sha256": file_sha(args.model / "model.safetensors"),
            "config_sha256": file_sha(args.model / "config.json"),
            "source_implementations": {
                "modeling": module_source("transformers.models.gemma4.modeling_gemma4"),
                "audio_feature_extraction": module_source(
                    "transformers.models.gemma4.feature_extraction_gemma4"
                ),
                "image_processing_reference": module_source(
                    "transformers.models.gemma4.image_processing_gemma4"
                ),
                "combined_processing_reference": module_source(
                    "transformers.models.gemma4.processing_gemma4"
                ),
                "e2_foreign_mouth": {
                    "path": Path(__file__).resolve().as_posix(),
                    "sha256": file_sha(Path(__file__).resolve()),
                },
            },
        },
        "apparatus": {
            "device": torch.cuda.get_device_name(0),
            "compute_capability": list(torch.cuda.get_device_capability(0)),
            "cpu_semantic_replay": False,
            "precomputed_feature_file": False,
            "organs_resident_sequentially_under_one_product_owner": True,
        },
        "vision": vision,
        "audio": audio,
        "text": text,
        "video": video,
    }
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
