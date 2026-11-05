#!/usr/bin/env python3
"""The sections a lap walks last, and their answers' lengths (§16.47, the unified-theory reading of November 5, 12:31).

Usage: walked.py TRAIN.txt KEYS READ...

Reproduces the trainer's sections (`sections_of`: the withheld first in a keyed order, the rest sorted by question and
answer length in bytes, cut in sections of 16) and a lap's walk (`walk`, keyed by the learner's lap count `read`), with
`mix` the trainer's. For each READ (the lap count the lap walked under: the next lap line's `read` less one), the mean
answer length of the last 1, 4, 16 and 64 sections walked, beside the passage's mean. Reading only; nothing here is a text.
"""
import sys

M = (1 << 64) - 1
KS = (1, 2, 4, 8, 16, 32, 64, 128)


def mix(seed, counter):
    z = (seed + counter * 0x9E3779B97F4A7C15) & M
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M
    return z ^ (z >> 31)


def problems_of(text):
    lines = text.split(b"\n")
    blocks, cur = [], []
    for line in lines:
        if line == b"":
            blocks.append(cur)
            cur = []
        else:
            cur.append(line)
    blocks.append(cur)
    return [(b[0], b"\n".join(b[1:])) for b in blocks if len(b) >= 2]


def main():
    text = open(sys.argv[1], "rb").read()
    keys = open(sys.argv[2], "rb").read()
    seed = int.from_bytes(keys[-8:], "big")
    probs = problems_of(text)
    n = len(probs)
    keyed = sorted(range(n), key=lambda i: (mix(seed, 1 << 61 | i), i))
    rest = keyed[128:]
    rest.sort(key=lambda i: (len(probs[i][0]) + 1 + len(probs[i][1]), i))
    sections = [rest[k:k + 16] for k in range(0, len(rest), 16)]
    alen = lambda s: sum(len(probs[i][1]) for i in sections[s]) / len(sections[s])
    mean = sum(len(probs[i][1]) for i in rest) / len(rest)
    print(f"problems {n}, trained {len(rest)}, sections {len(sections)}, passage mean answer {mean:.1f} bytes")
    print("read\t" + "\t".join(f"last{k}" for k in KS) + "\t(each the mean answer length less the passage's)")
    for read in map(int, sys.argv[3:]):
        walk = sorted(range(len(sections)), key=lambda s: (mix(seed, ((read << 40) ^ s) & M), s))
        out = []
        for k in KS:
            last = walk[-k:]
            m = sum(alen(s) * len(sections[s]) for s in last) / sum(len(sections[s]) for s in last)
            out.append(f"{m - mean:+.1f}")
        print(f"{read}\t" + "\t".join(out))


if __name__ == "__main__":
    main()
