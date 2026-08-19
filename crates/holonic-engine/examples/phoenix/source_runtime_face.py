#!/usr/bin/env python
"""The source runtime's own face of layer zero, EMITTED as exact bit patterns for the resident driver
to compare against its certified enclosures — the exterior half of the cross-chart defect slot.

This is exterior realization testimony and never governs the native result (Gemma instance
blueprint §6: "an exterior source-runtime replay may provide an independent comparison face and
never governs the native result"). It runs the authoritative `Gemma4TextDecoderLayer` for layer 0
on the token identities the resident driver was handed, in two dtypes — bfloat16, which is the
source's declared dtype and rounds every intermediate, and float32, which is nearer the exact
mathematics — and writes the values at six named ports as the exact bit patterns of their float64
promotion, one line per coordinate:

    port dtype index hex64

The driver reads this file, decodes every value through its exact float mouth, and returns
`chi_gamma = Phi_Y T_gamma - S_gamma Phi_X` per coordinate against the resident enclosure of the
same port. Nothing here is a gate.

    /home/b/scratch/huggingface/.venv/bin/python crates/holonic-engine/examples/phoenix/source_runtime_face.py \
        --tokens 818,18740 --emit /path/to/faces.tsv
"""

import argparse
import struct

import torch
from safetensors import safe_open
from transformers import AutoConfig
from transformers.models.gemma4.modeling_gemma4 import (
    Gemma4RMSNorm,
    Gemma4TextDecoderLayer,
    Gemma4TextRotaryEmbedding,
)

ROOT = "/home/b/models/gemma-4-E4B-it"
LAYER = 0
PREFIX = f"model.language_model.layers.{LAYER}."


def face(dtype, tokens):
    cfg = AutoConfig.from_pretrained(ROOT).text_config
    torch.manual_seed(0)
    layer = Gemma4TextDecoderLayer(cfg, LAYER)
    with safe_open(f"{ROOT}/model.safetensors", framework="pt") as f:
        state = {k[len(PREFIX):]: f.get_tensor(k) for k in f.keys() if k.startswith(PREFIX)}
        _, unexpected = layer.load_state_dict(state, strict=False)
        assert not unexpected, unexpected
        embed = f.get_slice("model.language_model.embed_tokens.weight")
        rows = torch.stack([embed[t : t + 1][0] for t in tokens])  # [T, 2560] bf16
        ple_table = f.get_slice("model.language_model.embed_tokens_per_layer.weight")
        ple_rows = torch.stack([ple_table[t : t + 1][0] for t in tokens])  # [T, 10752]
        proj = f.get_slice("model.language_model.per_layer_model_projection.weight")
        proj_rows = proj[LAYER * 256 : (LAYER + 1) * 256]  # [256, 2560]
        proj_norm_w = f.get_tensor("model.language_model.per_layer_projection_norm.weight")
    layer = layer.to(dtype)
    embed_scale = torch.tensor(cfg.hidden_size**0.5).to(torch.bfloat16)
    x0 = (rows.to(dtype) * embed_scale.to(dtype)).unsqueeze(0)  # [1, T, 2560]
    ple_scale = torch.tensor(cfg.hidden_size_per_layer_input**0.5).to(torch.bfloat16)
    tok = (ple_rows.to(dtype) * ple_scale.to(dtype))[:, LAYER * 256 : (LAYER + 1) * 256].unsqueeze(0)
    projected = torch.nn.functional.linear(x0, proj_rows.to(dtype)) * (cfg.hidden_size**-0.5)
    norm = Gemma4RMSNorm(cfg.hidden_size_per_layer_input, eps=cfg.rms_norm_eps)
    norm.weight.data = proj_norm_w.to(dtype)
    projected = norm(projected)
    per_layer_input = (projected + tok) * (2.0**-0.5)
    T = len(tokens)
    position_ids = torch.arange(T).unsqueeze(0)
    rotary = Gemma4TextRotaryEmbedding(cfg)
    cos, sin = rotary(x0, position_ids, layer_type=cfg.layer_types[LAYER])
    mask = torch.full((1, 1, T, T), float("-inf"), dtype=dtype)
    mask = torch.triu(mask, diagonal=1)

    captured = {}

    def keep(name):
        def hook(module, inputs, output):
            captured[name] = output.detach().to(torch.float64)
        return hook

    def keep_input(name):
        def hook(module, inputs):
            captured[name] = inputs[0].detach().to(torch.float64)
        return hook

    hooks = [
        layer.input_layernorm.register_forward_hook(keep("input-rebase")),
        layer.self_attn.q_proj.register_forward_hook(keep("receiver-projection")),
        layer.self_attn.o_proj.register_forward_pre_hook(keep_input("contact")),
        layer.post_attention_layernorm.register_forward_hook(keep("post-attention-rebase")),
        layer.post_feedforward_layernorm.register_forward_hook(keep("post-feedforward-rebase")),
    ]
    with torch.no_grad():
        out = layer(
            x0,
            per_layer_input,
            shared_kv_states={},
            position_embeddings=(cos, sin),
            attention_mask=mask,
            position_ids=position_ids,
        )
    for hook in hooks:
        hook.remove()
    # The two re-entries, in the source's own dtype arithmetic: residual + returned, then rounded
    # exactly as the source rounds them.
    r1 = (x0.to(dtype) + captured["post-attention-rebase"].to(dtype)).to(torch.float64)
    r2 = (r1.to(dtype) + captured["post-feedforward-rebase"].to(dtype)).to(torch.float64)
    faces = {
        "input-rebase": captured["input-rebase"],
        "receiver-projection": captured["receiver-projection"],
        "contact": captured["contact"],
        "first-re-entry": r1,
        "second-re-entry": r2,
        "layer": out[0].to(torch.float64),
    }
    return {name: value.reshape(-1) for name, value in faces.items()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tokens", required=True)
    parser.add_argument("--emit", required=True)
    args = parser.parse_args()
    tokens = [int(t) for t in args.tokens.split(",")]
    with open(args.emit, "w") as out:
        out.write("# port dtype index hex64 — the source runtime's face of layer 0, tokens %s\n" % tokens)
        for dtype, name in ((torch.bfloat16, "bf16"), (torch.float32, "f32")):
            faces = face(dtype, tokens)
            for port, values in faces.items():
                for at, value in enumerate(values.tolist()):
                    bits = struct.unpack("<Q", struct.pack("<d", value))[0]
                    out.write(f"{port} {name} {at} {bits:016x}\n")
    print(f"emitted {args.emit}")


if __name__ == "__main__":
    main()
