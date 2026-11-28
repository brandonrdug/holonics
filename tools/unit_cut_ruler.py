#!/usr/bin/env -S python3 -I
"""unit_cut_ruler.py ROWS FOUNDED CUT [CUT_CONTROL]: a ruler (the lead, November 28; the review's build step 1, its probe of F1). Whether
a founded unit met again is cut whole.

FOUNDED is a crossing's receipt (`found-units`' `OUT.founded.tsv`: each founded run's octets in hex, a line); CUT a `read-epochs` (or
`read-strand-cut`) output (`cut.tsv`: a row, its places, its anchors). For each founded run, every place it stands in the rows of ROWS
(each row's octets as `read-reach` reads them) is a meeting; a meeting is cut whole where the cut has an anchor at its first place and at
the place after its last, and none inside. Read by the run's length (and, of the meetings whose first place the cut anchors, the share
cut whole: a run met inside a longer word is no meeting of the unit), and beside it the same meetings in CUT_CONTROL (a cut through a
state with no units: how often her news alone cuts the same spans whole). Outside the machine; counts.
"""
import sys
from collections import defaultdict


def rows_of(path):
    texts = []
    for line in open(path, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append(b''.join(bytes.fromhex(t[4:]) if t.startswith('hex:') else t.replace('\\n', '\n').encode() for t in f[1:3]))
    return texts


def cuts_of(path):
    out = {}
    for line in open(f'{path}/cut.tsv'):
        f = line.rstrip('\n').split('\t')
        out[int(f[0])] = (int(f[1]), {int(a) for a in f[2].split(',') if a})
    return out


def whole(cut, r, s, e):
    n, anchors = cut[r]
    if e > n:
        return None
    return s in anchors and (e in anchors or e == n) and not any(a in anchors for a in range(s + 1, e))


def main():
    texts = rows_of(sys.argv[1])
    founded = [bytes.fromhex(line.strip()) for line in open(sys.argv[2]) if line.strip()]
    cut = cuts_of(sys.argv[3])
    control = cuts_of(sys.argv[4]) if len(sys.argv) > 4 else None
    tally = defaultdict(lambda: [0, 0, 0])
    started = defaultdict(lambda: [0, 0])  # meetings whose first place the cut anchors, and of them the whole
    for u in founded:
        L = min(len(u), 8)
        for r, t in enumerate(texts):
            if r not in cut:
                continue
            i = t.find(u)
            while i != -1:
                w = whole(cut, r, i, i + len(u))
                if w is not None:
                    tally[L][0] += 1
                    tally[L][1] += w
                    if i in cut[r][1]:
                        started[L][0] += 1
                        started[L][1] += w
                    if control is not None and r in control:
                        tally[L][2] += bool(whole(control, r, i, i + len(u)))
                i = t.find(u, i + 1)
    print(f"UNIT_CUT founded={len(founded)} lengths={','.join(str(sum(1 for u in founded if min(len(u), 8) == L)) for L in range(2, 9))}")
    tot = [0, 0, 0]
    for L in sorted(tally):
        m, w, c = tally[L]
        tot = [tot[0] + m, tot[1] + w, tot[2] + c]
        sm, sw = started[L]
        print(f"UNIT_CUT length={L} meetings={m} whole={w / max(m, 1):.3f}" + (f" whole_without_units={c / max(m, 1):.3f}" if control else "") + f" started={sm} whole_given_started={sw / max(sm, 1):.3f}")
    print(f"UNIT_CUT all meetings={tot[0]} whole={tot[1] / max(tot[0], 1):.3f}" + (f" whole_without_units={tot[2] / max(tot[0], 1):.3f}" if control else ""))


if __name__ == '__main__':
    main()
