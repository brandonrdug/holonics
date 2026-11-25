#!/usr/bin/env -S python3 -I
"""A count ruler on one specimen of a sampled propagation (recorded speech): what a place's rank among K levels of equal mass
tells of the place n back, at K levels and at three sample clocks, and a place's code with both neighbours known.
Usage: levels_ruler.py LIBRISPEECH_DIR"""
import json, os, subprocess, sys
import numpy as np
RINGS = [2, 3, 4, 9, 16, 27, 32, 81, 128, 243, 256, 729, 1024]
def lag_info(runs, k, n):
    joint = np.zeros(k * k, dtype=np.int64)
    for s in runs:
        if len(s) > n: joint += np.bincount(s[n:].astype(np.int64) * k + s[:-n], minlength=k * k)
    tot = joint.sum()
    if tot == 0: return None
    p = joint.reshape(k, k) / tot; px = p.sum(1); py = p.sum(0); m = p > 0
    i = float((p[m] * np.log(p[m] / np.outer(px, py)[m])).sum())
    return i - (np.count_nonzero(px) - 1) * (np.count_nonzero(py) - 1) / (2 * tot)
def cloze(runs, k):
    """H(u_t | u_(t-1), u_(t+1)) by counts, add-1/2 within a context (KT)."""
    c = np.zeros(k ** 3, dtype=np.int64)
    for s in runs:
        s = s.astype(np.int64)
        if len(s) > 2: c += np.bincount((s[:-2] * k + s[2:]) * k + s[1:-1], minlength=k ** 3)
    c = c.reshape(k * k, k).astype(np.float64); n = c.sum(1, keepdims=True)
    p = (c + 0.5) / (n + k / 2)
    return float(-(c * np.log(p)).sum() / c.sum())
def before(runs, k):
    """H(u_t | u_(t-1), u_(t-2))."""
    c = np.zeros(k ** 3, dtype=np.int64)
    for s in runs:
        s = s.astype(np.int64)
        if len(s) > 2: c += np.bincount((s[:-2] * k + s[1:-1]) * k + s[2:], minlength=k ** 3)
    c = c.reshape(k * k, k).astype(np.float64); n = c.sum(1, keepdims=True)
    p = (c + 0.5) / (n + k / 2)
    return float(-(c * np.log(p)).sum() / c.sum())
root = sys.argv[1]
rows = [json.loads(l) for l in open(os.path.join(root, "train-clean-100.manifest.jsonl"))]
by = {}
for r in rows: by.setdefault(r["speaker_id"], []).append(r)
speakers = sorted(by)[::16]
picked = [r for s in speakers for r in sorted(by[s], key=lambda r: r["id"])[:3]]
def path_of(r):
    p = r["flac_path"]
    return os.path.join(root, "source", "LibriSpeech", "train-clean-100", p)
print("picked", len(picked), "speakers", len(speakers), flush=True)
for rate in (16000, 8000, 4000):
    waves = []
    for r in picked:
        raw = subprocess.run(["ffmpeg", "-v", "error", "-i", path_of(r), "-ar", str(rate), "-f", "s16le", "-"], capture_output=True, check=True).stdout
        waves.append(np.frombuffer(raw, dtype="<i2"))
    allw = np.concatenate(waves)
    print(f"RATE {rate} samples {len(allw)} seconds {len(allw)/rate:.1f}", flush=True)
    for k in (3, 9, 13, 16):
        cuts = np.quantile(allw, [i / k for i in range(1, k)]).astype(np.int64)
        runs = [np.searchsorted(cuts, w, side="right").astype(np.int16) for w in waves]
        cat = np.concatenate(runs); p = np.bincount(cat, minlength=k) / len(cat)
        h = float(-(p[p > 0] * np.log(p[p > 0])).sum())
        info = " ".join(f"{n}:{lag_info(runs, k, n):.4f}" for n in [1] + RINGS)
        print(f"LEVELS rate={rate} k={k} entropy={h:.4f} of={np.log(k):.4f} cloze={cloze(runs, k):.4f} before2={before(runs, k):.4f} cuts={' '.join(map(str, cuts))}")
        print(f"  LAG {info}", flush=True)
