#!/usr/bin/env -S python3 -I
"""rise_cut_ruler.py SAMPLE_ROWS SAMPLE_CODES ROWS CODES OUT: a ruler (the lead, November 28; the formal thread's rise cut of 00:58 UTC,
G-Z62). Where a span's ends are by its type: her news after each run, as a mean over the run's meetings, and a cut where that mean rises.

SAMPLE_CODES and CODES are `read-reach … law` outputs (`codes.tsv`: a row, its group, a place, her code there on `2^(−20)` bits) of
SAMPLE_ROWS and ROWS (`read-far`'s table). Over the sample, each run `s` of 1 to 8 octets ending at a place `t` gathers her code at
`t + 1`, so `ν̄(s)` is the mean news after `s` over its meetings (the branching after it, as her face reads it) with its count. On ROWS,
at each place the runs ending there join by their counts, `ν̂(t) = Σ_k n_k ν̄(s_k) / Σ_k n_k` (a run never met has no weight), and an
end stands after `t` where `ν̂(t) > ν̂(t − 1)`, the rise (`rise`); beside it the peak (`peak`: a rise with no rise after it). Each form's
anchors go to `OUT/<form>/cut.tsv` (a row, its places, its anchors), the form `tools/epoch_cut_ruler.py` reads. Outside the machine;
counts and means.
"""
import os
import sys
from collections import defaultdict

DEPTH = 8


def rows_of(path):
    texts = []
    for line in open(path, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append(b''.join(bytes.fromhex(t[4:]) if t.startswith('hex:') else t.replace('\\n', '\n').encode() for t in f[1:3]))
    return texts


def codes_of(path, n_rows):
    out = [dict() for _ in range(n_rows)]
    for line in open(f'{path}/codes.tsv'):
        f = line.rstrip('\n').split('\t')
        out[int(f[0])][int(f[2])] = int(f[3])
    return out


def main():
    sample, sample_codes, rows, codes, out = sys.argv[1:6]
    st = rows_of(sample)
    sc = codes_of(sample_codes, len(st))
    total, count = defaultdict(int), defaultdict(int)
    for r, t in enumerate(st):
        c = sc[r]
        for p in range(len(t) - 1):
            if p + 1 not in c:
                continue
            for k in range(1, DEPTH + 1):
                if p - k + 1 < 0:
                    break
                s = t[p - k + 1:p + 1]
                total[s] += c[p + 1]
                count[s] += 1
    print(f"RISE_CUT runs={len(count)} meetings={sum(count.values())}")
    texts = rows_of(rows)
    for form in ('rise', 'peak'):
        os.makedirs(f'{out}/{form}', exist_ok=True)
    lines = {'rise': [], 'peak': []}
    epochs = {'rise': 0, 'peak': 0}
    for r, t in enumerate(texts):
        n = len(t)
        nu = []
        for p in range(n):
            num = den = 0
            for k in range(1, DEPTH + 1):
                if p - k + 1 < 0:
                    break
                s = t[p - k + 1:p + 1]
                if s in count:
                    num += total[s]
                    den += count[s]
            nu.append(num / den if den else None)
        rise = [p > 0 and nu[p] is not None and nu[p - 1] is not None and nu[p] > nu[p - 1] for p in range(n)]
        anchors = {'rise': [0], 'peak': [0]}
        for p in range(n - 1):
            if rise[p]:
                anchors['rise'].append(p + 1)
                if not (p + 1 < n and rise[p + 1]):
                    anchors['peak'].append(p + 1)
        for form in ('rise', 'peak'):
            a = sorted(set(anchors[form]))
            epochs[form] += len(a)
            lines[form].append(f"{r}\t{n}\t{','.join(map(str, a))}\n")
    for form in ('rise', 'peak'):
        with open(f'{out}/{form}/cut.tsv', 'w') as f:
            f.writelines(lines[form])
        places = sum(len(t) for t in texts)
        print(f"RISE_CUT form={form} places={places} anchors={epochs[form]} places_an_epoch={places / max(epochs[form], 1):.2f}")


if __name__ == '__main__':
    main()
