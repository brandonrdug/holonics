#!/usr/bin/env -S python3 -I
"""A count ruler on a wave slice: a held place's code, in nats, under count tables taken on the training documents (add-1/2 within a
context), with one, two and four neighbours known; and with none. Documents are read on their own (no context crosses a document's end).
Usage: held_count_ruler.py SLICE_DIR NAME [TRAIN_DOCUMENTS]"""
import os, sys
import numpy as np
out, name = sys.argv[1], sys.argv[2]
limit = int(sys.argv[3]) if len(sys.argv) > 3 else None
chart = [l.split("\t") for l in open(os.path.join(out, f"CHART_{name}.tsv")).read().rstrip("\n").split("\n")[1:]]
k = len(chart); level = np.full(256, -1, dtype=np.int64)
for r in chart: level[int(r[1])] = int(r[0])
def docs(stem, limit=None):
    idx = [int(l.split("\t")[2]) for l in open(os.path.join(out, f"{stem}_{name}.tsv")).read().rstrip("\n").split("\n")[1:]]
    with open(os.path.join(out, f"{stem}_{name}.bin"), "rb") as f:
        for n in idx[:limit]:
            yield level[np.frombuffer(f.read(n), dtype=np.uint8)]
FORMS = {"none": (), "one back": (-1,), "two back": (-2, -1), "both sides": (-1, 1), "two each side": (-2, -1, 1, 2)}
def keys(s, offs):
    lo, hi = max([0] + [-o for o in offs]), max([0] + [o for o in offs])
    n = len(s) - lo - hi
    key = np.zeros(n, dtype=np.int64)
    for o in offs: key = key * k + s[lo + o:lo + o + n]
    return key * k + s[lo:lo + n]
tables = {f: np.zeros(k ** (len(o) + 1), dtype=np.int64) for f, o in FORMS.items()}
places = 0
for s in docs("DOCS", limit):
    places += len(s)
    for f, o in FORMS.items(): tables[f] += np.bincount(keys(s, o), minlength=k ** (len(o) + 1))
print(f"COUNT_TABLES levels={k} training_places={places}")
code = {f: 0.0 for f in FORMS}; n_held = {f: 0 for f in FORMS}
logp = {}
for f in FORMS:
    c = tables[f].reshape(-1, k).astype(np.float64)
    logp[f] = np.log((c + 0.5) / (c.sum(1, keepdims=True) + k / 2)).reshape(-1)
for s in docs("HELD"):
    for f, o in FORMS.items():
        kk = keys(s, o); code[f] -= float(logp[f][kk].sum()); n_held[f] += len(kk)
for f in FORMS:
    print(f"HELD_CODE known={f!r:18} nats_a_place={code[f] / n_held[f]:.4f} places={n_held[f]}")
