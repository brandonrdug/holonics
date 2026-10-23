# Split the repeat after ">>" into its first digit and the following digits, per arm.
# usage: python3 -I repeat_split.py TRAIN_JSONL PARTITION_JSON N BYTES_F32x3
import json, re, sys, numpy as np
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
idx = json.load(open(sys.argv[2]))["train_indices"][:int(sys.argv[3])]
bb = np.fromfile(sys.argv[4], dtype="<f4").reshape(-1, 3)
first, rest, pos = [], [], 0
for ri in idx:
    r = rows[ri]
    q, a = r["question"].encode(), r["answer"].encode()
    off = pos + len(q) + 1
    for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", a):
        j, k = m.end(), 0
        while j < len(a) and (48 <= a[j] <= 57 or a[j] in b".,"):
            if 48 <= a[j] <= 57:
                (first if k == 0 else rest).append(off + j); k += 1
            j += 1
    pos = off + len(a) + 2
assert pos == len(bb)
for name, sel in (("first digit after >>", first), ("following digits", rest)):
    print("%-22s %6d" % (name, len(sel)) + "".join("  %6.3f" % bb[sel, i].mean() for i in range(3)) + "  (base node ring, bits a byte)")
