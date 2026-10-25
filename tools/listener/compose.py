#!/usr/bin/env python3
"""Compose GSM8K, MNIST and LibriSpeech into one class passage for the tower (`tower_classes.rs`).

Usage: python3 -I tools/listener/compose.py CONFIG.json OUT_DIR

Every item is one section, as in `examples/listener/sections.rs`: a source passage through its
boundary chart, the end letter, a target, the end letter. The charts are `micro.py`'s (the same
octets as `sections.rs`): text as its octets, a raster as its stroke (eighth-turns and intensity
octaves), PCM as its half-cycles (run length, sign and peak octave). The exact fibres (intensity
remainders, sample residuals) stay at the boundary and are not written. Classes `0..256` are the
octets and `256` the end letter, which no octet writes; a class file holds each class as a
big-endian `u16`.

Which sections and in what order is exterior codec information, declared in CONFIG and the
manifest, never learner material:
- GSM8K: `question` then `answer`, from the train partition (`tools/gsm8k/partition.py`);
- MNIST: an image then its label numeral, and for every other training image the label first and
  the image second, so the tower hears both directions of one pairing;
- LibriSpeech: an utterance's PCM then its transcript, and for every other training utterance the
  transcript first, the training and held-out utterances from disjoint speakers.
The media are interleaved so that each keeps its share along the passage: the next section is
taken from the medium furthest behind its share, so every stream the tower cuts holds all three.

Written: `train.classes`, `dev.classes` and per medium `{text,digit,sound}.{train,dev}.classes`
(the siblings); `dev.roles` (one byte a class: 0 GSM8K, 1 stroke, 2 half-cycles, 3 the numerals and
transcripts paired with an image or sound); `dev.marks` (one byte a class, for `read-tower-classes`:
1 a held-out label numeral read after its image, 2 a GSM8K answer, 3 a GSM8K question, 4 a
transcript read after its sound, 5 a stroke, 6 a half-cycle octet, 7 an end letter, 8 a numeral or
transcript heard before its image or sound); the prompts (`prompts.*.classes`), and
`MANIFEST.json` with every input's and output's SHA-256.
"""

import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import micro  # noqa: E402  the boundary charts, shared with sections.rs

END = 256


def digest(data):
    return hashlib.sha256(data).hexdigest()


def classes_bytes(classes):
    return b"".join(struct.pack(">H", c) for c in classes)


def section(source, source_role, source_mark, target, target_role, target_mark):
    """`source END target END` with each class's role and mark; an end letter takes its passage's role."""
    classes = list(source) + [END] + list(target) + [END]
    roles = [source_role] * (len(source) + 1) + [target_role] * (len(target) + 1)
    marks = [source_mark] * len(source) + [7] + [target_mark] * len(target) + [7]
    return classes, roles, marks


def gsm8k(cfg, base):
    rows = [json.loads(line) for line in open(base / cfg["train_jsonl"], encoding="utf-8")]
    partition = json.load(open(base / cfg["partition"]))
    def made(indices):
        out = []
        for i in indices:
            q, a = rows[i]["question"].encode(), rows[i]["answer"].encode()
            out.append(section(q, 0, 3, a, 0, 2))
        return out
    return made(partition["train_indices"][: cfg["train"]]), made(partition["dev_indices"][: cfg["dev"]])


def mnist(cfg, base):
    images = (base / cfg["images"]).read_bytes()
    labels = (base / cfg["labels"]).read_bytes()
    count, height, width = struct.unpack(">III", images[4:16])
    if struct.unpack(">I", labels[4:8])[0] != count:
        raise ValueError("MNIST images and labels differ in count")
    def item(i):
        pixels = list(images[16 + i * height * width: 16 + (i + 1) * height * width])
        octets, _ = micro.stroke(width, height, pixels)
        return octets, str(labels[8 + i]).encode()
    train, dev = [], []
    for k, i in enumerate(range(cfg["train_from"], cfg["train_from"] + cfg["train"])):
        strokes, label = item(i)
        train.append(section(strokes, 1, 5, label, 3, 1) if k % 2 == 0 else section(label, 3, 8, strokes, 1, 5))
    for i in range(cfg["dev_from"], cfg["dev_from"] + cfg["dev"]):
        strokes, label = item(i)
        dev.append(section(strokes, 1, 5, label, 3, 1))
    return train, dev


def pcm_of(path):
    raw = subprocess.run(["ffmpeg", "-v", "error", "-i", str(path), "-f", "s16le", "-ac", "1", "-"], capture_output=True, check=True).stdout
    return list(struct.unpack("<%dh" % (len(raw) // 2), raw))


def librispeech(cfg, base):
    root = base / cfg["root"]
    speakers = sorted((p for p in root.iterdir() if p.is_dir()), key=lambda p: int(p.name))
    held = speakers[-cfg["dev_speakers"]:]
    utterances = {"train": [], "dev": []}
    for side, group in (("train", speakers[: -cfg["dev_speakers"]]), ("dev", held)):
        for speaker in group:
            for chapter in sorted(speaker.iterdir(), key=lambda p: int(p.name)):
                for line in open(chapter / f"{speaker.name}-{chapter.name}.trans.txt", encoding="utf-8"):
                    uid, text = line.rstrip("\n").split(" ", 1)
                    utterances[side].append((uid, chapter / f"{uid}.flac", text.encode()))
    def take(side, seconds_cap, budget_samples, order_both):
        out, ids, total = [], [], 0
        for uid, path, text in utterances[side]:
            if total >= budget_samples:
                break
            samples = pcm_of(path)
            if len(samples) > seconds_cap * cfg["rate"]:
                continue
            octets, _ = micro.half_cycles(cfg["rate"], samples)
            k = len(out)
            out.append(section(octets, 2, 6, text, 3, 4) if (not order_both or k % 2 == 0) else section(text, 3, 8, octets, 2, 6))
            ids.append({"utterance": uid, "samples": len(samples), "chart_octets": len(octets), "transcript": text.decode()})
            total += len(samples)
        return out, ids
    train, train_ids = take("train", cfg["max_seconds"], cfg["train_seconds"] * cfg["rate"], True)
    dev, dev_ids = take("dev", cfg["max_seconds"], cfg["dev_seconds"] * cfg["rate"], False)
    return train, dev, train_ids, dev_ids, [p.name for p in held]


def interleave(media):
    """The next section from the medium furthest behind its share of the passage's classes."""
    totals = {m: sum(len(s[0]) for s in secs) for m, secs in media.items() if secs}
    at = {m: 0 for m in totals}
    done = {m: 0 for m in totals}
    out = []
    while any(at[m] < len(media[m]) for m in totals):
        m = min((m for m in totals if at[m] < len(media[m])), key=lambda m: (done[m] * 10**6 // totals[m], m))
        s = media[m][at[m]]
        out.append(s)
        done[m] += len(s[0])
        at[m] += 1
    return out


def flat(sections):
    classes, roles, marks = [], [], []
    for c, r, k in sections:
        classes += c
        roles += r
        marks += k
    return classes, roles, marks


def main(argv):
    config_path, out = Path(argv[1]), Path(argv[2])
    cfg = json.load(open(config_path))
    base = config_path.parent
    out.mkdir()
    text_train, text_dev = gsm8k(cfg["gsm8k"], base)
    digit_train, digit_dev = mnist(cfg["mnist"], base)
    sound_train, sound_dev, sound_train_ids, sound_dev_ids, held_speakers = librispeech(cfg["librispeech"], base)
    media_train = {"text": text_train, "digit": digit_train, "sound": sound_train}
    media_dev = {"text": text_dev, "digit": digit_dev, "sound": sound_dev}
    written = {}
    def write(name, data):
        (out / name).write_bytes(data)
        written[name] = {"bytes": len(data), "sha256": digest(data)}
    for side, media in (("train", media_train), ("dev", media_dev)):
        classes, roles, marks = flat(interleave(media))
        write(f"{side}.classes", classes_bytes(classes))
        if side == "dev":
            write("dev.roles", bytes(roles))
            write("dev.marks", bytes(marks))
        for m, secs in media.items():
            c, r, k = flat(secs)
            write(f"{m}.{side}.classes", classes_bytes(c))
            if side == "dev":
                write(f"{m}.dev.roles", bytes(r))
                write(f"{m}.dev.marks", bytes(k))
    # Prompts: each a source passage and its end letter; the tower writes until its end letter.
    prompts = {
        "text": [s[0][: s[0].index(END) + 1] for s in text_dev[: cfg["prompts"]["text"]]],
        "label": [s[0][: s[0].index(END) + 1] for s in digit_dev[: cfg["prompts"]["label"]]],
        "digit": [list(str(d).encode()) + [END] for d in range(10)],
        "transcript": [s[0][: s[0].index(END) + 1] for s in sound_dev[: cfg["prompts"]["sound"]]],
        "speech": [list(u["transcript"].encode()) + [END] for u in sound_dev_ids[: cfg["prompts"]["sound"]]],
    }
    for name, ps in prompts.items():
        write(f"prompts.{name}.classes", classes_bytes([c for p in ps for c in p]))
    counts = {side: {m: {"sections": len(secs), "classes": sum(len(s[0]) for s in secs)} for m, secs in media.items()} for side, media in (("train", media_train), ("dev", media_dev))}
    manifest = {
        "config": cfg,
        "config_sha256": digest(config_path.read_bytes()),
        "inputs": {k: digest((base / v).read_bytes()) for k, v in (("gsm8k_train_jsonl", cfg["gsm8k"]["train_jsonl"]), ("gsm8k_partition", cfg["gsm8k"]["partition"]), ("mnist_images", cfg["mnist"]["images"]), ("mnist_labels", cfg["mnist"]["labels"]))},
        "sound_decoder": subprocess.run(["ffmpeg", "-version"], capture_output=True, text=True).stdout.splitlines()[0],
        "sound_held_out_speakers": held_speakers,
        "sound_train": sound_train_ids,
        "sound_dev": sound_dev_ids,
        "counts": counts,
        "written": written,
    }
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=1) + "\n")
    print(json.dumps(counts))


if __name__ == "__main__":
    main(sys.argv)
