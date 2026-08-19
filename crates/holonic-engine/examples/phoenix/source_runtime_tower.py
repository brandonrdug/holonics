#!/usr/bin/env python
"""The source runtime's own face of the WHOLE text tower — exterior realization testimony for the
resident tower deed, emitted as exact bit patterns, never governing the native result.

Two commands:

    python source_runtime_tower.py encode "text one" "text two" ...
        -> one line per text: the token identities the source tokenizer assigns (JSON list), with
           the BOS the source prepends. The tokenizer is an exterior codec asset (tokenizer.json),
           used here as apparatus and declared USED by the resident driver for the encoding only.

    python source_runtime_tower.py face --tokens a,b,c --emit /path/faces.tsv [--top 32]
        -> the source's bf16 forward over the token identities: the residual stream after each
           layer at every position, the final normed standing, the logits at every position (the
           last position whole, earlier positions as their top-k), and the decoded surfaces of the
           top-k at the last position. Every value is the float64 bit pattern of the bf16 face, one
           line per coordinate:  kind  index  position  hex64   (or for surfaces: token id, text)

The source is run in its declared dtype (bfloat16); a float32 face of the whole tower does not fit
the machine's memory and is not emitted. Nothing here is a gate.
"""
import argparse
import json
import struct
import sys

ROOT = "/home/b/models/gemma-4-E4B-it"


def hex64(value):
    return "%016x" % struct.unpack("<Q", struct.pack("<d", float(value)))[0]


def encode(texts):
    from transformers import AutoTokenizer
    tokenizer = AutoTokenizer.from_pretrained(ROOT)
    for text in texts:
        ids = tokenizer(text, add_special_tokens=True)["input_ids"]
        print(json.dumps({"text": text, "ids": ids, "pieces": tokenizer.convert_ids_to_tokens(ids)}))


def decode_ids(ids):
    from transformers import AutoTokenizer
    tokenizer = AutoTokenizer.from_pretrained(ROOT)
    for i in ids:
        print(json.dumps({"id": i, "piece": tokenizer.convert_ids_to_tokens([i])[0], "text": tokenizer.decode([i])}))


def face(tokens, emit, top):
    import torch
    from transformers import AutoTokenizer, Gemma4ForConditionalGeneration
    torch.manual_seed(0)
    tokenizer = AutoTokenizer.from_pretrained(ROOT)
    model = Gemma4ForConditionalGeneration.from_pretrained(ROOT, dtype=torch.bfloat16, low_cpu_mem_usage=True)
    model.eval()
    ids = torch.tensor([tokens], dtype=torch.long)
    with torch.no_grad():
        out = model(input_ids=ids, output_hidden_states=True, return_dict=True)
    hidden = out.hidden_states  # tuple: embeddings, then after each layer; the last is post final norm in HF? (check)
    logits = out.logits[0]  # [T, V] bf16 (softcapped)
    T = ids.shape[1]
    with open(emit, "w") as f:
        f.write("# kind\tindex\tposition\thex64\n")
        # hidden_states: [embeddings(after scale), layer0 out, ..., layer41 out] — HF appends the final normed state as the last entry for Gemma4TextModel? We emit all and label by index.
        for li, h in enumerate(hidden):
            h = h[0].to(torch.float64)
            for t in range(T):
                row = h[t]
                for i in range(row.shape[0]):
                    f.write(f"hidden{li}\t{i}\t{t}\t{hex64(row[i].item())}\n")
        last = logits[T - 1].to(torch.float64)
        for v in range(last.shape[0]):
            f.write(f"logits\t{v}\t{T-1}\t{hex64(last[v].item())}\n")
        for t in range(T - 1):
            row = logits[t].to(torch.float64)
            values, indices = torch.topk(row, top)
            for value, index in zip(values.tolist(), indices.tolist()):
                f.write(f"topk\t{index}\t{t}\t{hex64(value)}\n")
        values, indices = torch.topk(last, top)
        for rank, (value, index) in enumerate(zip(values.tolist(), indices.tolist())):
            piece = tokenizer.convert_ids_to_tokens([index])[0]
            text = tokenizer.decode([index])
            f.write(f"surface\t{index}\t{rank}\t{json.dumps({'piece': piece, 'text': text, 'hex64': hex64(value)})}\n")
    print(json.dumps({"tokens": tokens, "hidden_states": len(hidden), "positions": T, "vocab": int(logits.shape[1]), "emitted": emit}))


def vision(emit):
    """A deterministic synthetic image through the source's processor and vision tower; emits the
    tower's last hidden state (the soft tokens, pre-embedder) and the embedder's output (the
    projection into the shared stream) as exact bit patterns of their bf16 values."""
    import torch
    from PIL import Image
    import numpy as np
    from transformers import Gemma4ForConditionalGeneration
    from transformers.models.gemma4.image_processing_pil_gemma4 import Gemma4ImageProcessorPil
    torch.manual_seed(0)
    processor_config = json.load(open(f"{ROOT}/processor_config.json"))["image_processor"]
    processor_config = {k: v for k, v in processor_config.items() if k not in ("image_processor_type",)}
    image_processor = Gemma4ImageProcessorPil(**processor_config)
    model = Gemma4ForConditionalGeneration.from_pretrained(ROOT, dtype=torch.bfloat16, low_cpu_mem_usage=True)
    model.eval()
    # a deterministic image: horizontal hue gradient over vertical brightness, 256 x 256
    h = np.broadcast_to(np.arange(256, dtype=np.float32)[None, :] / 255.0, (256, 256))
    v = np.broadcast_to(np.arange(256, dtype=np.float32)[:, None] / 255.0, (256, 256))
    rgb = np.stack([(h * 255), (v * 255), ((1 - h) * v * 255)], axis=-1).astype(np.uint8)
    image = Image.fromarray(rgb, mode="RGB")
    inputs = image_processor(images=image, return_tensors="pt")
    pixel_values = inputs["pixel_values"].to(torch.bfloat16)
    image_position_ids = inputs["image_position_ids"]
    with torch.no_grad():
        features = model.model.get_image_features(pixel_values=pixel_values, image_position_ids=image_position_ids)
    last = features.last_hidden_state.to(torch.float64)
    pooled = features.pooler_output.to(torch.float64)
    print(json.dumps({"last_hidden_state_shape": list(last.shape), "pooler_output_shape": list(pooled.shape)}), file=sys.stderr)
    last = last.reshape(-1, last.shape[-1])      # [N, 768]
    pooled = pooled.reshape(-1, pooled.shape[-1])  # [N, 2560]
    with open(emit, "w") as f:
        f.write("# kind\tindex\tposition\thex64\n")
        for t in range(last.shape[0]):
            for i in range(last.shape[1]):
                f.write(f"soft\t{i}\t{t}\t{hex64(last[t, i].item())}\n")
        for t in range(pooled.shape[0]):
            for i in range(pooled.shape[1]):
                f.write(f"projected\t{i}\t{t}\t{hex64(pooled[t, i].item())}\n")
    print(json.dumps({"soft_tokens": int(last.shape[0]), "soft_width": int(last.shape[1]), "projected_width": int(pooled.shape[1]), "pixel_values": list(pixel_values.shape), "emitted": emit}))


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    e = sub.add_parser("encode"); e.add_argument("texts", nargs="+")
    d = sub.add_parser("decode"); d.add_argument("ids", type=int, nargs="+")
    f = sub.add_parser("face"); f.add_argument("--tokens", required=True); f.add_argument("--emit", required=True); f.add_argument("--top", type=int, default=32)
    v = sub.add_parser("vision"); v.add_argument("--emit", required=True)
    args = parser.parse_args()
    if args.command == "encode":
        encode(args.texts)
    elif args.command == "decode":
        decode_ids(args.ids)
    elif args.command == "vision":
        vision(args.emit)
    else:
        face([int(t) for t in args.tokens.split(",")], args.emit, args.top)


if __name__ == "__main__":
    main()
