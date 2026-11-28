#!/usr/bin/env -S python3 -I
"""expected_peak_ruler.py SAMPLE_ROWS SAMPLE_CODES ROWS FACES OUT: a ruler (the lead, November 28; the formal thread's G-Z77 of 10:58
UTC). The rise store's peak named in time by expectation: an end after `t` where the rise at `t` is not expected to continue under her
face, `E_(p_(t+1)) ν̂(t + 1 | x) ≤ ν̂(t)`, beside the peak that reads the symbol at `t + 1` (the strand's open-news law of November 18).

`ν̂` is the type cut's: her mean news after the runs of one and two octets ending at a place over the sample (`SAMPLE_CODES` a
`read-reach … law` output), the depths joined by their counts. FACES is a `read-reach … faces:all` output on ROWS (her face whole at
every place from the second, each class's code on `2^(−20)` bits): the face at place `t + 1` gives the density of the octet there, its
classes of one octet read as that octet (any other class's mass is left out and the density renormalized). Each form's anchors go to
`OUT/<form>/cut.tsv`, and the share of the peak's ends the expected form keeps (and of its own that stand in the peak's) is printed.
Outside the machine; floats at the exterior.
"""
import math
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from rise_cut_ruler import codes_of, rows_of  # noqa: E402

LN2_20 = math.log(2) / (1 << 20)


def main():
    sample, sample_codes, rows, faces, out = sys.argv[1:6]
    st = rows_of(sample)
    sc = codes_of(sample_codes, len(st))
    total, count = defaultdict(int), defaultdict(int)
    for r, t in enumerate(st):
        c = sc[r]
        for p in range(len(t) - 1):
            if p + 1 not in c:
                continue
            for k in (1, 2):
                if p - k + 1 < 0:
                    break
                s = t[p - k + 1:p + 1]
                total[s] += c[p + 1]
                count[s] += 1

    def nu_hat(prev, a):
        num = den = 0
        for s in ((a,), (prev, a)) if prev is not None else ((a,),):
            s = bytes(s)
            if s in count:
                num += total[s]
                den += count[s]
        return num / den if den else None

    # her faces: classes of one octet, by place
    classes = []
    for line in open(f'{faces}/classes.tsv'):
        f = line.rstrip('\n').split('\t')
        if len(f) >= 2:
            classes.append(f[1])
    octet = [int(h, 16) if len(h) == 2 else -1 for h in classes]
    single = np.array([o >= 0 for o in octet])
    index = [tuple(int(v) for v in line.split('\t')[:3]) for line in open(f'{faces}/faces.tsv')]
    raw = np.memmap(f'{faces}/faces.i32', dtype='<i4', mode='r', shape=(len(index), len(classes)))
    face_at = {}
    for i, (r, t, _) in enumerate(index):
        face_at[(r, t)] = i
    texts = rows_of(rows)
    # her mean news after each possible next octet given the octet at t: a table on the host, a ruler's
    nu_next = {}
    lines = {'peak': [], 'expected': [], 'counted': []}
    kept = inside = ends_p = ends_e = 0
    kept_c = ends_c = 0
    # beside it, the expectation under the store's own counts of what follows the octet at t (a type's, no face)
    follow = defaultdict(lambda: defaultdict(int))
    for s_ in count:
        if len(s_) == 2:
            follow[s_[0]][s_[1]] = count[s_]
    counted_next = {}
    for r, t in enumerate(texts):
        n = len(t)
        nu = [nu_hat(t[p - 1] if p > 0 else None, t[p]) for p in range(n)]
        rise = [p > 0 and (a := nu[p]) is not None and (b := nu[p - 1]) is not None and a > b for p in range(n)]
        peak, exp, cnt = [0], [0], [0]
        for p in range(n - 1):
            if not rise[p]:
                continue
            if not rise[p + 1]:
                peak.append(p + 1)
            if t[p] not in counted_next:
                num = den = 0.0
                for o, k in follow[t[p]].items():
                    v_ = nu_hat(t[p], o)
                    if v_ is not None:
                        num += k * v_
                        den += k
                counted_next[t[p]] = num / den if den else None
            ce = counted_next[t[p]]
            if ce is not None and ce <= (nu[p] or 0.0):
                cnt.append(p + 1)
            i = face_at.get((r, p + 1))
            if i is None:
                continue
            if t[p] not in nu_next:
                v = np.array([(nu_hat(t[p], o) if o >= 0 else None) or 0.0 for o in octet])
                m = np.array([o >= 0 and nu_hat(t[p], o) is not None for o in octet])
                nu_next[t[p]] = (v, m)
            v, m = nu_next[t[p]]
            logp = -np.asarray(raw[i], dtype=np.float64) * LN2_20
            use = single & m
            w = np.exp(logp[use] - logp[use].max())
            expect = float((w * v[use]).sum() / w.sum())
            if expect <= (nu[p] or 0.0):
                exp.append(p + 1)
        a, b = set(peak), set(exp)
        kept += len(a & b)
        inside += len(a & b)
        ends_p += len(a)
        ends_e += len(b)
        kept_c += len(a & set(cnt))
        ends_c += len(cnt)
        lines['counted'].append(f"{r}\t{n}\t{','.join(map(str, cnt))}\n")
        lines['peak'].append(f"{r}\t{n}\t{','.join(map(str, peak))}\n")
        lines['expected'].append(f"{r}\t{n}\t{','.join(map(str, exp))}\n")
    places = sum(len(t) for t in texts)
    for form, ls in lines.items():
        os.makedirs(f'{out}/{form}', exist_ok=True)
        with open(f'{out}/{form}/cut.tsv', 'w') as f:
            f.writelines(ls)
    print(f"EXPECTED_PEAK places={places} peak_ends={ends_p} expected_ends={ends_e} places_an_epoch={places / max(ends_e, 1):.2f} "
          f"kept={kept / max(ends_p, 1):.3f} in_peak={inside / max(ends_e, 1):.3f}")
    print(f"EXPECTED_PEAK form=counted counted_ends={ends_c} places_an_epoch={places / max(ends_c, 1):.2f} kept={kept_c / max(ends_p, 1):.3f} "
          f"in_peak={kept_c / max(ends_c, 1):.3f}")


if __name__ == '__main__':
    main()
