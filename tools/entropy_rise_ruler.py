#!/usr/bin/env -S python3 -I
"""entropy_rise_ruler.py SAMPLE_ROWS SAMPLE_FACES ROWS FACES OUT: a ruler (the lead, November 28; the formal thread's G-Z66 of 01:28 UTC).
The rise cut with the store holding only what her face lacks: cross-entropy is entropy plus divergence, so the news after a run is her
face's own entropy there plus a store's mean of the rest.

SAMPLE_FACES and FACES are `read-reach … faces:all` outputs (her face whole at every place from the second, each class's code on
`2^(−20)` bits, and the written class). At each place `t` her face's entropy `H_t` (the expected code under it, renormalized) and her news
`ν_t` (the written symbol's code) are read; over the sample each run `s` of 1 or 2 octets ending at `t − 1` gathers `ν_t − H_t`, so
`δ̄(s)` is its mean over the run's meetings. On ROWS, `ν̂(p) = H_(p+1) + δ̄`, the depths joined by their counts, and an end stands after `p`
where `ν̂` peaks (a rise with no rise after it; the rise beside it), each form's anchors to `OUT/<form>/cut.tsv`. Outside the machine;
floats at the exterior.
"""
import math
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from rise_cut_ruler import rows_of  # noqa: E402

LN2_20 = math.log(2) / (1 << 20)
DEPTHS = (1, 2)


def read_faces(fd):
    """Each row's places' (entropy, news) in nats, by row and place, from a faces:all dump."""
    alphabet = len(open(f'{fd}/classes.tsv').read().split('\n')) - 1
    index = [tuple(int(v) for v in line.split('\t')[:3]) for line in open(f'{fd}/faces.tsv')]
    raw = np.memmap(f'{fd}/faces.i32', dtype='<i4', mode='r', shape=(len(index), alphabet))
    out = defaultdict(dict)
    step = 20000
    for a in range(0, len(index), step):
        c = np.asarray(raw[a:a + step], dtype=np.float64) * LN2_20
        logp = -c
        logp -= logp.max(1, keepdims=True)
        logp -= np.log(np.exp(logp).sum(1, keepdims=True))
        h = -(np.exp(logp) * logp).sum(1)
        for i in range(len(c)):
            r, t, y = index[a + i]
            out[r][t] = (h[i], -logp[i, y])
    return out


def main():
    sample, sample_faces, rows, faces, out = sys.argv[1:6]
    st = rows_of(sample)
    sf = read_faces(sample_faces)
    total, count = defaultdict(float), defaultdict(int)
    for r, t in enumerate(st):
        for p, (h, nu) in sf[r].items():
            for k in DEPTHS:
                if p - k < 0:
                    break
                s = t[p - k:p]
                total[s] += nu - h
                count[s] += 1
    print(f"ENTROPY_RISE runs={len(count)} meetings={sum(count.values())} mean_divergence={sum(total.values()) / max(sum(count.values()), 1):.4f}")
    texts = rows_of(rows)
    hf = read_faces(faces)
    lines = {'rise': [], 'peak': []}
    ends = {'rise': 0, 'peak': 0}
    for r, t in enumerate(texts):
        n = len(t)
        nu = []
        for p in range(n):
            if p + 1 not in hf[r]:
                nu.append(None)
                continue
            num = den = 0.0
            for k in DEPTHS:
                if p - k + 1 < 0:
                    break
                s = t[p - k + 1:p + 1]
                if s in count:
                    num += total[s]
                    den += count[s]
            nu.append(hf[r][p + 1][0] + (num / den if den else 0.0))
        rise = [p > 0 and nu[p] is not None and nu[p - 1] is not None and nu[p] > nu[p - 1] for p in range(n)]
        anchors = {'rise': [0], 'peak': [0]}
        for p in range(n - 1):
            if rise[p]:
                anchors['rise'].append(p + 1)
                if not (p + 1 < n and rise[p + 1]):
                    anchors['peak'].append(p + 1)
        for form in ('rise', 'peak'):
            ends[form] += len(anchors[form])
            lines[form].append(f"{r}\t{n}\t{','.join(map(str, anchors[form]))}\n")
    places = sum(len(t) for t in texts)
    for form in ('rise', 'peak'):
        os.makedirs(f'{out}/{form}', exist_ok=True)
        with open(f'{out}/{form}/cut.tsv', 'w') as f:
            f.writelines(lines[form])
        print(f"ENTROPY_RISE form={form} places={places} anchors={ends[form]} places_an_epoch={places / max(ends[form], 1):.2f}")


if __name__ == '__main__':
    main()
