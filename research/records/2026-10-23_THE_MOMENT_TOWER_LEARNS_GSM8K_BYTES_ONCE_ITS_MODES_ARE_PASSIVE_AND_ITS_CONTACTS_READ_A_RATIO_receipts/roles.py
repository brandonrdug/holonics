# Coarse regions of a rendered GSM8K partition ("question\nanswer\n\n" per problem), as the
# mathematics thread's prep.py: 0 Q question (with its newline), 1 P answer text outside the
# calculations except digits (with the closing blank line), 2 N answer digits outside the
# calculations, 3 M calculation markup <<...>>.
# usage: python3 -I roles.py TRAIN_JSONL PARTITION_JSON KEY PASSAGE OUT
import json, re, sys
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
idx = json.load(open(sys.argv[2]))[sys.argv[3]]
passage = open(sys.argv[4], "rb").read()
buf, coarse = bytearray(), bytearray()
for ri in idx:
    r = rows[ri]
    q, a = r["question"].encode(), r["answer"].encode()
    buf += q + b"\n" + a + b"\n\n"
    coarse += bytes([0] * (len(q) + 1))
    ac = [2 if 48 <= c <= 57 else 1 for c in a]
    for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", a):
        for i in range(m.start(), m.end()):
            ac[i] = 3
    coarse += bytes(ac + [1, 1])
    if len(buf) >= len(passage):
        break
assert bytes(buf[:len(passage)]) == passage, "rendering differs from the passage"
open(sys.argv[5], "wb").write(bytes(coarse[:len(passage)]))
print("bytes", len(passage), "Q P N M", [coarse[:len(passage)].count(k) for k in range(4)])
