"""Exterior upper bound on what the question can tell the field's context read.

In the context read an answer byte a_i is open and the three bytes on each side are resolved
(they lie in A_res, the resolved sites). For the open sites A_open of one part,

    I(Q; A_open | A_res) <= H(A_open | A_res) <= sum_i H(a_i | A_res) <= sum_i H(a_i | l3_i, r3_i)

(subadditivity, then conditioning on less), and a held-out model's cross-entropy is at least the
entropy it estimates. So the held-out cross-entropy of a 3+3 neighbour model, averaged over
answer bytes, bounds from above the question's information per answer byte in that read, however
well a learner reads the question. The model is Witten-Bell interpolation over the contexts
(l3,r3), (l2,r2), (l1,r1) and none, fit on the problems whose index is not divisible by 5 and read
on the rest. Exterior reading only: no learner, no generation, no acceptance.

Usage: python3 -I bound.py TRAIN_JSONL
"""

import json
import math
import re
import sys
from collections import Counter, defaultdict

RUN = re.compile(rb"[A-Za-z0-9]+")
CONTEXT = 4
PAD = 2  # a byte absent from GSM8K text, standing for "outside the answer"
LEVELS = (3, 2, 1)


def ctx(a, i, k):
    left = bytes(a[j] if j >= 0 else PAD for j in range(i - k, i))
    right = bytes(a[j] if j < len(a) else PAD for j in range(i + 1, i + 1 + k))
    return (k, left, right)


def classes(q, a):
    q_runs = {m.group() for m in RUN.finditer(q)}
    where = {}
    occ = defaultdict(list)
    for m in RUN.finditer(a):
        s, e, w = m.start(), m.end(), m.group()
        occ[w].append(s)
        for i in range(s, e):
            where[i] = (i - s, w, s)
    out = []
    for i in range(len(a)):
        r = i % CONTEXT
        if i not in where:
            out.append("glue")
            continue
        off, w, s = where[i]
        kind = "digit" if w.isdigit() else "word"
        if any(s2 != s and (s2 + off) % CONTEXT != r for s2 in occ[w]):
            out.append("restated_" + kind)
        elif w in q_runs:
            out.append("qonly_" + kind)
        else:
            out.append("new_" + kind)
    return out


def main(path):
    rows = [json.loads(line) for line in open(path, encoding="utf-8")]
    count = Counter()  # (context, x) -> n
    total = Counter()  # context -> n
    kinds = defaultdict(set)  # context -> distinct x
    uni = Counter()
    for idx, row in enumerate(rows):
        if idx % 5 == 0:
            continue
        a = row["answer"].encode("utf-8")
        for i, x in enumerate(a):
            uni[x] += 1
            for k in LEVELS:
                c = ctx(a, i, k)
                count[(c, x)] += 1
                total[c] += 1
                kinds[c].add(x)
    n_uni = sum(uni.values())

    def prob(a, i, x):
        p = (uni[x] + 1) / (n_uni + 256)
        for k in reversed(LEVELS):
            c = ctx(a, i, k)
            t = len(kinds[c]) if c in kinds else 0
            n = total[c]
            if n == 0:
                continue
            p = (count[(c, x)] + t * p) / (n + t)
        return p

    bits = Counter()
    seen = Counter()
    for idx, row in enumerate(rows):
        if idx % 5 != 0:
            continue
        q = row["question"].encode("utf-8")
        a = row["answer"].encode("utf-8")
        cl = classes(q, a)
        for i, x in enumerate(a):
            b = -math.log2(prob(a, i, x))
            bits[cl[i]] += b
            seen[cl[i]] += 1
            bits["all"] += b
            seen["all"] += 1
    n_all = seen["all"]
    print(f"held-out problems {sum(1 for i in range(len(rows)) if i % 5 == 0)}  answer bytes {n_all}")
    print("class            share   bits/byte(class)  contribution to the all-byte mean")
    for k in sorted(seen, key=lambda k: -bits[k]):
        if k == "all":
            continue
        print(f"  {k:16s} {seen[k] / n_all:6.4f}  {bits[k] / seen[k]:8.4f}          {bits[k] / n_all:7.4f}")
    print(f"  all              1.0000  {bits['all'] / n_all:8.4f}")
    q_part = sum(bits[k] for k in bits if k.startswith("qonly") or k.startswith("new"))
    print(f"  qonly+new contribution {q_part / n_all:7.4f} bits per answer byte")


if __name__ == "__main__":
    main(sys.argv[1])
