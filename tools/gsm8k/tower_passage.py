"""The tower's GSM8K passage (record 2026-10-30_THE_COARSE_LEVEL_HEADS…, §43).

    python3 -I tools/gsm8k/tower_passage.py TRAIN_JSONL PARTITION_JSON OUT_DIR
"""
# GSM8K passage for the tower (record 2026-10-30 §43): each problem "question" END "answer" END, END the
# record separator 0x1E; roles per byte 0 Q (question and its END), 1 P (answer prose and its END),
# 2 N (answer digits outside the calculations), 3 M (calculation markup <<...>>). Also the written
# rules' texts (problems separated by a blank line) and the flux prompts (the first six development
# questions, each closed by END).
import json, re, sys, hashlib
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
part = json.load(open(sys.argv[2])); import os; os.chdir(sys.argv[3])
END = b"\x1e"
def render(idx):
    buf, roles = bytearray(), bytearray()
    for i in idx:
        q, a = rows[i]["question"].encode(), rows[i]["answer"].encode()
        buf += q + END + a + END
        roles += bytes([0] * (len(q) + 1))
        ac = [2 if 48 <= c <= 57 else 1 for c in a]
        for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", a):
            for k in range(m.start(), m.end()):
                ac[k] = 3
        roles += bytes(ac + [1])
    return bytes(buf), bytes(roles)
def text(idx):
    return "".join(rows[i]["question"] + "\n" + rows[i]["answer"] + "\n\n" for i in idx).encode()
train, dev = part["train_indices"], part["dev_indices"]
tb, _ = render(train); db, dr = render(dev)
open("TRAIN.bytes", "xb").write(tb); open("DEV.bytes", "xb").write(db); open("DEV.roles", "xb").write(dr)
open("TRAIN.txt", "xb").write(text(train)); open("HELD128.txt", "xb").write(text(dev[:128]))
open("PROMPTS6.bytes", "xb").write(b"".join(rows[i]["question"].encode() + END for i in dev[:6]))
for n in ["TRAIN.bytes", "DEV.bytes", "DEV.roles", "TRAIN.txt", "HELD128.txt", "PROMPTS6.bytes"]:
    d = open(n, "rb").read(); print(n, len(d), hashlib.sha256(d).hexdigest())
print("roles Q P N M", [dr.count(k) for k in range(4)])
