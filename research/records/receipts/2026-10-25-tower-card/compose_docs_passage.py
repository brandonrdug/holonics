"""The declared passage of the card's parity and rate reads (agent-inferred, October 25).

docs/*.md in path order, each octet one class of the 257-class alphabet (two bytes a class,
big-endian), with the end letter 256 after every file and after the first blank line ("\n\n")
that closes 4 KiB or more since the last end letter. The held-out passage is README.md the same
way, its roles all region 0. The founding keys are SHA-256 of b"athena-card-keys" and a 64-bit
big-endian counter, concatenated. Run from the repository root: python3 compose_docs_passage.py OUT
"""
import glob, hashlib, struct, sys, os

END = 256
SPAN = 4096


def classes(paths):
    out = []
    for path in paths:
        data = open(path, "rb").read()
        since = 0
        i = 0
        while i < len(data):
            out.append(data[i])
            since += 1
            if since >= SPAN and data[i] == 0x0A and i > 0 and data[i - 1] == 0x0A:
                out.append(END)
                since = 0
            i += 1
        out.append(END)
    return out


def write(path, cls):
    with open(path, "xb") as f:
        f.write(b"".join(struct.pack(">H", c) for c in cls))


out = sys.argv[1]
os.makedirs(out, exist_ok=True)
train = classes(sorted(glob.glob("docs/*.md")))
dev = classes(["README.md"])
write(os.path.join(out, "TRAIN.classes"), train)
write(os.path.join(out, "DEV.classes"), dev)
with open(os.path.join(out, "DEV.roles"), "xb") as f:
    f.write(bytes(len(dev)))
keys = b"".join(hashlib.sha256(b"athena-card-keys" + struct.pack(">Q", i)).digest() for i in range(1 << 15))
with open(os.path.join(out, "KEYS"), "xb") as f:
    f.write(keys)
print(f"train_classes={len(train)} train_ends={train.count(END)} dev_classes={len(dev)} keys_bytes={len(keys)}")
