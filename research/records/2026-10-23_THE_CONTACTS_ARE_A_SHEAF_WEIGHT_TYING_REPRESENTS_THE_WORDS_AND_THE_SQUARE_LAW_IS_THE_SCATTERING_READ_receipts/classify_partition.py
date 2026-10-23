# Per-byte code grouped by role, for the partition rendering "question\nanswer\n\n" (two separators).
# usage: python3 -I classify_partition.py TRAIN_JSONL PARTITION_JSON N BYTES_F32x3 NAME0 NAME1 NAME2
import json, re, sys, numpy as np
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
idx = json.load(open(sys.argv[2]))["train_indices"][:int(sys.argv[3])]
bb = np.fromfile(sys.argv[4], dtype="<f4").reshape(-1, 3)
arms = [(sys.argv[5 + i], bb[:, i]) for i in range(3)]
roles = []
for ri in idx:
    r = rows[ri]
    q, a = r["question"].encode(), r["answer"].encode()
    lab = ["question digit" if 48 <= ch <= 57 else "question prose" for ch in q]
    lab.append("separator")
    al = ["answer prose"] * len(a)
    for i, ch in enumerate(a):
        if 48 <= ch <= 57: al[i] = "answer digit (prose)"
    for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", a):
        for i in range(m.start(), m.end()): al[i] = "calc markup"
        for i in range(m.start(1), m.end(1)):
            if 48 <= a[i] <= 57: al[i] = "calc operand digit"
        for i in range(m.start(2), m.end(2)):
            if 48 <= a[i] <= 57: al[i] = "calc result digit"
        j = m.end()
        while j < len(a) and (48 <= a[j] <= 57 or a[j] in b".,"):
            if 48 <= a[j] <= 57: al[j] = "digit after >> (repeat of result)"
            j += 1
    h = a.rfind(b"#### ")
    if h >= 0:
        for i in range(h, h + 5): al[i] = "#### marker"
        for i in range(h + 5, len(a)):
            if 48 <= a[i] <= 57: al[i] = "final answer digit"
    lab += al
    lab += ["separator", "separator"]
    roles += lab
roles = np.array(roles)
assert len(roles) == len(bb), (len(roles), len(bb))
names = sorted(set(roles), key=lambda k: -arms[0][1][roles == k].sum())
print("%-34s %8s" % ("role", "bytes") + "".join("  %-12s" % n for n, _ in arms) + "  (bits a byte)")
for k in names:
    sel = roles == k
    print("%-34s %8d" % (k, sel.sum()) + "".join("  %12.3f" % b[sel].mean() for n, b in arms))
print("%-34s %8d" % ("all", len(roles)) + "".join("  %12.3f" % b.mean() for n, b in arms))
