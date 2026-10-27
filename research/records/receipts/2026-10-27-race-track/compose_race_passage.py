"""The race track's declared passage (agent-inferred, October 27).

Train: every Markdown file under docs/ and research/records/ (subdirectories included) in path
order, except the held-out ones, then the GSM8K training text. Each octet is one class of the
257-class alphabet (two bytes a class, big-endian), with the end letter 256 after every file and
after the first blank line ("\\n\\n") that closes 4 KiB or more since the last end letter: the
October 25 passage's rule (receipts/2026-10-25-tower-card/compose_docs_passage.py), so a file is
read as it is written and nothing about its medium is authored.

Held out, with the held-out read's roles: README.md and the records dated October 26 and 27,
role 3; the GSM8K development text, role 0. Founding keys as on October 25: SHA-256 of
b"athena-card-keys" and a 64-bit big-endian counter, concatenated.

Prompts (each closes with its end letter, as `release-tower-classes` reads them): the first
end-lettered span of README.md, of the first held-out record and of the GSM8K development text,
each twice. Release keys: SHA-256 of b"athena-race-release" and a counter, concatenated, COUNT
eight-byte keys a prompt; the same keys every lap, so laps differ only by the learner.

Run from the repository root:
python3 compose_race_passage.py OUT GSM8K_TRAIN GSM8K_DEV COUNT
"""
import glob, hashlib, os, struct, sys

END = 256
SPAN = 4096


def classes(data):
    out, since = [], 0
    for i, b in enumerate(data):
        out.append(b)
        since += 1
        if since >= SPAN and b == 0x0A and i > 0 and data[i - 1] == 0x0A:
            out.append(END)
            since = 0
    out.append(END)
    return out


def first_span(cls):
    return cls[: cls.index(END) + 1]


def write(path, cls):
    with open(path, "xb") as f:
        f.write(b"".join(struct.pack(">H", c) for c in cls))


def digests(tag, n):
    return b"".join(hashlib.sha256(tag + struct.pack(">Q", i)).digest() for i in range(n))


out, gsm_train, gsm_dev, count = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
os.makedirs(out, exist_ok=True)
held = sorted(glob.glob("research/records/2026-10-2[67]_*.md"))
markdown = sorted(set(glob.glob("docs/**/*.md", recursive=True)) | set(glob.glob("research/records/**/*.md", recursive=True)))
markdown = [p for p in markdown if p not in held]
read = lambda p: open(p, "rb").read()
train = [c for p in markdown for c in classes(read(p))] + classes(read(gsm_train))
prose = [c for p in ["README.md"] + held for c in classes(read(p))]
gsm = classes(read(gsm_dev))
dev = gsm + prose
roles = bytes(len(gsm)) + bytes([3]) * len(prose)
prompts = []
for source in (classes(read("README.md")), classes(read(held[0])), gsm):
    prompts += first_span(source) * 2
write(os.path.join(out, "TRAIN.classes"), train)
write(os.path.join(out, "DEV.classes"), dev)
with open(os.path.join(out, "DEV.roles"), "xb") as f:
    f.write(roles)
with open(os.path.join(out, "KEYS"), "xb") as f:
    f.write(digests(b"athena-card-keys", 1 << 15))
write(os.path.join(out, "PROMPTS.classes"), prompts)
with open(os.path.join(out, "RELEASE_KEYS"), "xb") as f:
    f.write(digests(b"athena-race-release", (6 * count * 8 + 31) // 32))
print(f"files={len(markdown)} held={len(held) + 1} train_classes={len(train)} train_ends={train.count(END)} "
      f"dev_classes={len(dev)} gsm8k_dev={len(gsm)} prose_dev={len(prose)} prompts={prompts.count(END)} prompt_classes={len(prompts)}")
