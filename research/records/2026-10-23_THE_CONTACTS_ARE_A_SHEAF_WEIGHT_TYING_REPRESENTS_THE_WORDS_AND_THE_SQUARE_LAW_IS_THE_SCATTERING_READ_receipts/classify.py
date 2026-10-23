# Where the code length goes: per-byte bits (sum of the byte's four cells) grouped by the byte's role
# in a GSM8K problem rendered "question\nanswer\n". Roles are read from the text's own markup.
import json, re, sys, numpy as np
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")][:int(sys.argv[2])]
arms = [(name, np.fromfile(path, dtype="<f4")) for name, path in zip(sys.argv[3::2], sys.argv[4::2])]
roles = []
for r in rows:
    q, a = r["question"].encode(), r["answer"].encode()
    lab = []
    for ch in q:
        lab.append("question digit" if 48 <= ch <= 57 else "question prose")
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
    lab.append("separator")
    roles += lab
roles = np.array(roles)
assert len(roles) == len(arms[0][1]), (len(roles), len(arms[0][1]))
names = sorted(set(roles), key=lambda k: -arms[0][1][roles == k].sum())
tot = {n: b.sum() for n, b in arms}
print("%-36s %8s" % ("role", "bytes") + "".join("  %-26s" % (n + ": bits/byte, share") for n, _ in arms))
for k in names:
    sel = roles == k
    print("%-36s %8d" % (k, sel.sum()) + "".join("  %8.3f %6.1f%%            " % (b[sel].mean(), 100 * b[sel].sum() / tot[n]) for n, b in arms))
print("%-36s %8d" % ("all", len(roles)) + "".join("  %8.3f                   " % (b.mean()) for n, b in arms))
