"""Cut a terrain of the public Holonics text for the tower: four media heard together, the dated
records' prose, the Framework's Lean, the main library's Rust and the terrain of interacting digits
(`arithmetic_terrain.py`), so arithmetic is one section of what the tower hears and not its subject.

Each text medium is its tracked files in path order (`git ls-files` at the checkout), read at a
stride so the cut spans the whole tree: training takes the files at `k * stride` and the held-out
text the files at `k * stride + stride // 2`, never a training file. From each chosen file the cut
takes whole lines from its start until it holds `GRAIN` bytes or the file ends, then the next file,
until the medium's share is filled; so a file's opening (its title, its module or namespace
comment, its first statements) is what is heard, and no line is cut. The arithmetic medium takes
whole lines from the start of an arithmetic terrain's `train.txt` and `dev.txt`.

Writes to OUT_DIR (which must not exist):
- train.txt: the four media's training shares one after another (prose, Lean, Rust, arithmetic),
  so the tower's contiguous streams each read mostly one medium and every section deposits all four
  together;
- dev.txt and dev.roles: the held-out shares in the same order, and one region byte per dev.txt
  byte, the medium's index (0 prose, 1 Lean, 2 Rust, 3 arithmetic; the tower's region names
  Q, P, N, M read here in that order);
- dev_prose.txt, dev_lean.txt, dev_rust.txt, dev_arithmetic.txt: each medium's held-out share
  alone, for reading its lines;
- MANIFEST.tsv: medium, part (train or dev), path, bytes taken, the taken bytes' SHA-256.

usage: python3 -I holonics_text_terrain.py CHECKOUT ARITHMETIC_DIR SHARE DEV_SHARE GRAIN OUT_DIR
"""
import hashlib
import os
import subprocess
import sys

MEDIA = [
    ("prose", "research/records/*.md", lambda p: p.count("/") == 2),
    ("lean", "lean/Holonics/*.lean", lambda p: True),
    ("rust", "crates/holonics/src/*.rs", lambda p: True),
]


def whole_lines(data, budget):
    """Whole lines from the start of `data` (each with its line end) while they fit `budget`; the
    first line is taken whatever its length."""
    lines, taken = [], 0
    for line in data.splitlines(keepends=True):
        if not line.endswith(b"\n"):
            line += b"\n"
        if taken and taken + len(line) > budget:
            break
        lines.append(line)
        taken += len(line)
    return b"".join(lines)


def cut(checkout, paths, offset, stride, share, grain):
    """Files at `offset + k * stride` in order, each read from its start to `grain` bytes of whole
    lines, until `share` bytes are held."""
    text, rows = b"", []
    k = offset
    while len(text) < share and k < len(paths):
        with open(os.path.join(checkout, paths[k]), "rb") as f:
            data = f.read()
        piece = whole_lines(data, min(grain, share - len(text)))
        if piece:
            text += piece
            rows.append((paths[k], len(piece), hashlib.sha256(piece).hexdigest()))
        k += stride
    if len(text) < share:
        sys.exit(f"the stride's files hold only {len(text)} of {share} bytes")
    return text, rows


def main():
    if len(sys.argv) != 7:
        sys.exit(__doc__)
    checkout, arithmetic, share, dev_share, grain, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    os.makedirs(out)
    train, dev, roles, manifest = b"", b"", b"", []
    for index, (name, pattern, keep) in enumerate(MEDIA):
        listed = subprocess.run(["git", "-C", checkout, "ls-files", pattern], check=True, capture_output=True, text=True).stdout.split()
        paths = sorted(p for p in listed if keep(p))
        # Twice the files both shares need at `grain` bytes a file, since a file may be shorter.
        stride = max(2, len(paths) // (2 * ((share + dev_share) // grain + 1)))
        t, t_rows = cut(checkout, paths, 0, stride, share, grain)
        d, d_rows = cut(checkout, paths, stride // 2, stride, dev_share, grain)
        manifest += [(name, "train", *r) for r in t_rows] + [(name, "dev", *r) for r in d_rows]
        train, dev, roles = train + t, dev + d, roles + bytes([index]) * len(d)
        with open(os.path.join(out, f"dev_{name}.txt"), "xb") as f:
            f.write(d)
    for part, budget in (("train", share), ("dev", dev_share)):
        with open(os.path.join(arithmetic, f"{part}.txt"), "rb") as f:
            piece = whole_lines(f.read(), budget)
        manifest.append(("arithmetic", part, f"{arithmetic}/{part}.txt", len(piece), hashlib.sha256(piece).hexdigest()))
        if part == "train":
            train += piece
        else:
            dev, roles = dev + piece, roles + bytes([3]) * len(piece)
            with open(os.path.join(out, "dev_arithmetic.txt"), "xb") as f:
                f.write(piece)
    for name, data in (("train.txt", train), ("dev.txt", dev), ("dev.roles", roles)):
        with open(os.path.join(out, name), "xb") as f:
            f.write(data)
        print(f"{name} bytes={len(data)} sha256={hashlib.sha256(data).hexdigest()}")
    with open(os.path.join(out, "MANIFEST.tsv"), "x") as f:
        for row in manifest:
            f.write("\t".join(str(x) for x in row) + "\n")
    for name in ("prose", "lean", "rust", "arithmetic"):
        with open(os.path.join(out, f"dev_{name}.txt"), "rb") as f:
            data = f.read()
        print(f"dev_{name}.txt bytes={len(data)} sha256={hashlib.sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
