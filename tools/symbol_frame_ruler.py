#!/usr/bin/env -S python3 -I
"""A ruler: a passage read under two changes of frame (the lead, November 17; Brandon's question of 00:18Z).

Usage: symbol_frame_ruler.py table STORE SLICE OUT_PREFIX   (writes OUT_PREFIX.{plain,renamed,doubled}.tsv)
       symbol_frame_ruler.py read DIR [DIR …]               (the codes of `read-tension` directories read from those tables)

A signature is what a change of frame leaves fixed. Two frames a reader of symbols should be able to locate inside one region:

- **renamed**: the letters of the region written through one fixed permutation of the alphabet (both cases alike), the professor's
  glyph: a substitution cipher whose menu is the region itself. A reader whose symbols are their use codes the region better the
  longer it is; a reader whose symbols are rows of their own does not.
- **doubled**: every byte written twice, the same passage at twice the raster. A reader with no privileged clock keeps its crossings:
  the second copy of a place is given by the first, and the first by what the passage gave before.

`table` cuts windows of 32, 64, 128, 256 and 512 places from the held documents of a store's slice (ASCII windows with no tab and
no backslash, so the table is plain text), and writes the three tables `read-tension` reads (`label<TAB>prompt<TAB>run<TAB>places`):
eight places a window opened alone, the same places in each frame, and for the doubled frame both copies of each. `read` prints, by
frame and window length, the count of places and the mean code in nats a place (for the doubled frame, the first and the second copy
apart). A ruler: it cuts and renames text outside the machine, and only counts and means leave the private store.
"""
import os
import random
import sys

LENGTHS = ((32, 48), (64, 48), (128, 32), (256, 24), (512, 12))
OPENED = 8
PROMPT = 4


def windows(store, slice_name):
    with open(os.path.join(store, f"HELD_{slice_name}.tsv")) as f:
        next(f)
        index = [tuple(int(x) for x in line.split("\t")) for line in f]
    data = open(os.path.join(store, f"HELD_{slice_name}.bin"), "rb").read()
    texts, at = [], 0
    for _, title, text, _, _ in index:
        texts.append(data[at + title:at + title + text])
        at += title + text
    rng = random.Random(20261117)
    out = {}
    for length, count in LENGTHS:
        found, tries = [], 0
        while len(found) < count and tries < 100000:
            tries += 1
            t = texts[rng.randrange(min(len(texts), 32))]
            if len(t) <= length:
                continue
            s = rng.randrange(len(t) - length)
            w = t[s:s + length]
            if all((32 <= b < 127 and b != 92) or b == 10 for b in w):
                found.append(w)
        out[length] = found
    return out


def escaped(b):
    return b.decode("ascii").replace("\n", "\\n")


def table(store, slice_name, prefix):
    rng = random.Random(1117)
    while True:
        perm = list(range(26))
        rng.shuffle(perm)
        if all(p != k for k, p in enumerate(perm)):
            break
    rename = {97 + k: 97 + p for k, p in enumerate(perm)}
    rename.update({65 + k: 65 + p for k, p in enumerate(perm)})
    cut = windows(store, slice_name)
    files = {name: open(f"{prefix}.{name}.tsv", "x") for name in ("plain", "renamed", "doubled")}
    for length, found in cut.items():
        places = [PROMPT + ((2 * k + 1) * (length - PROMPT)) // (2 * OPENED) for k in range(OPENED)]
        for n, w in enumerate(found):
            r = bytes(rename.get(b, b) for b in w)
            for name, text in (("plain", w), ("renamed", r)):
                files[name].write(f"sym:{name}:{length}:{n}\t{escaped(text[:PROMPT])}\t{escaped(text[PROMPT:])}\t{','.join(str(p - PROMPT) for p in places)}\n")
            if length <= 256:
                d = bytes(b for b in w for _ in (0, 1))
                both = [q for p in places for q in (2 * p, 2 * p + 1)]
                files["doubled"].write(f"sym:doubled:{length}:{n}\t{escaped(d[:PROMPT])}\t{escaped(d[PROMPT:])}\t{','.join(str(q - PROMPT) for q in both)}\n")
    for f in files.values():
        f.close()
    print("SYMBOL_FRAME_TABLE " + " ".join(f"{length}:{len(found)}" for length, found in cut.items()))


def read(dirs):
    import math
    acc = {}
    for d in dirs:
        for line in open(os.path.join(d, "rows.tsv")):
            label, place, tick, code = line.rstrip("\n").split("\t")[:4]
            if tick != "0":
                continue
            _, frame, length, _ = label.split(":")
            copy = "-" if frame != "doubled" else ("first" if (int(place) + PROMPT) % 2 == 0 else "second")
            e = acc.setdefault((frame, int(length), copy), [0, 0.0])
            e[0] += 1
            e[1] += int(code) / 2.0**20 * math.log(2.0)
    print("SYMBOL_FRAME frame window_places copy places nats_a_place")
    for key in sorted(acc):
        e = acc[key]
        print(f"SYMBOL_FRAME {key[0]} {key[1]} {key[2]} {e[0]} {e[1] / e[0]:.4f}")


if __name__ == "__main__":
    if len(sys.argv) >= 5 and sys.argv[1] == "table":
        table(sys.argv[2], sys.argv[3], sys.argv[4])
    elif len(sys.argv) >= 3 and sys.argv[1] == "read":
        read(sys.argv[2:])
    else:
        sys.exit(__doc__)
